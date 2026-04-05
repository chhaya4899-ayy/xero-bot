"""
XERO Bot — Database Adapter (PostgreSQL ↔ SQLite compatibility layer)
======================================================================
Makes asyncpg look exactly like aiosqlite so database.py needs zero SQL changes.

When DATABASE_URL is set → uses asyncpg (PostgreSQL — survives ALL Railway redeploys).
When DATABASE_URL is not set → falls through to aiosqlite (local dev/SQLite).

Translations applied automatically for PostgreSQL:
  ? placeholders          → $1, $2, $3, ...
  INSERT OR IGNORE        → INSERT ... ON CONFLICT DO NOTHING
  INSERT OR REPLACE       → INSERT ... ON CONFLICT DO NOTHING (safe fallback)
  INTEGER PK AUTOINCREMENT→ BIGINT GENERATED ALWAYS AS IDENTITY PRIMARY KEY
  DATETIME columns        → TIMESTAMP
  datetime('now')         → NOW()
  REAL columns            → DOUBLE PRECISION
  lastrowid               → via RETURNING * on INSERT
"""
import re
import os
import logging

try:
    import asyncpg
    _ASYNCPG_AVAILABLE = True
except ImportError:
    asyncpg = None  # type: ignore
    _ASYNCPG_AVAILABLE = False

logger = logging.getLogger("XERO.DBAdapter")
if not _ASYNCPG_AVAILABLE:
    logger.warning("asyncpg not installed — PostgreSQL unavailable, using SQLite fallback.")

DATABASE_URL: str | None = os.getenv("DATABASE_URL")


# ── Cursor ────────────────────────────────────────────────────────────────────

class _PGCursor:
    """Drop-in for aiosqlite cursor. Returned by _PGConn.execute()."""

    def __init__(self, rows: list, lastrowid=None):
        self._rows    = rows
        self.lastrowid = lastrowid  # matches aiosqlite cursor.lastrowid

    async def fetchone(self):
        return self._rows[0] if self._rows else None

    async def fetchall(self):
        return self._rows

    async def __aenter__(self):
        return self

    async def __aexit__(self, *_):
        pass


# ── Execute context (supports both `await` and `async with`) ──────────────────

class _PGExecContext:
    """
    Returned by _PGConn.execute().
    - `await db.execute(sql)` → runs statement, returns _PGCursor
    - `async with db.execute(sql) as c:` → runs statement, enters cursor context
    """

    __slots__ = ("_conn", "_sql", "_params", "_cursor")

    def __init__(self, conn: "asyncpg.Connection", sql: str, params: tuple):
        self._conn   = conn
        self._sql    = sql
        self._params = params
        self._cursor: _PGCursor | None = None

    async def _run(self) -> _PGCursor:
        sql    = self._sql
        params = self._params
        upper  = sql.strip().upper()

        if upper.startswith("SELECT"):
            rows = await self._conn.fetch(sql, *params)
            return _PGCursor(list(rows))

        elif upper.startswith("INSERT"):
            if "RETURNING" not in upper:
                returning_sql = sql.rstrip().rstrip(";") + " RETURNING *"
            else:
                returning_sql = sql
            try:
                rows = await self._conn.fetch(returning_sql, *params)
            except Exception:
                # ON CONFLICT DO NOTHING returns nothing — that's fine
                await self._conn.execute(sql, *params)
                return _PGCursor([])

            lastrowid = None
            if rows:
                r = rows[0]
                # Try common PK column names in priority order
                for col in ("id", "case_id", "ticket_id", "event_id",
                            "giveaway_id", "item_id", "warning_id",
                            "announcement_id"):
                    try:
                        lastrowid = r[col]
                        break
                    except KeyError:
                        pass
                if lastrowid is None:
                    # Fallback: first column
                    try:
                        lastrowid = r[0]
                    except Exception:
                        pass
            return _PGCursor(list(rows), lastrowid=lastrowid)

        else:
            await self._conn.execute(sql, *params)
            return _PGCursor([])

    # Supports: await db.execute(sql)
    def __await__(self):
        async def _inner():
            self._cursor = await self._run()
            return self._cursor
        return _inner().__await__()

    # Supports: async with db.execute(sql) as c:
    async def __aenter__(self) -> _PGCursor:
        self._cursor = await self._run()
        return self._cursor

    async def __aexit__(self, *_):
        pass


# ── Connection wrapper ─────────────────────────────────────────────────────────


class _PGConn:
    """
    Wraps a raw asyncpg Connection to behave like an aiosqlite Connection.
    Used inside _PGConnContext.__aenter__.
    """

    def __init__(self, conn: "asyncpg.Connection"):
        self._conn = conn

    # Stub for `db.row_factory = aiosqlite.Row` (no-op for PG)
    @property
    def row_factory(self): return None
    @row_factory.setter
    def row_factory(self, _): pass

    # ── SQL translation helpers ────────────────────────────────────────────

    @staticmethod
    def _translate_dml(sql: str, params=()) -> tuple[str, tuple]:
        """Translate aiosqlite DML → asyncpg DML."""
        or_ignore   = bool(re.search(r"\bOR\s+IGNORE\b",  sql, re.I))
        or_replace  = bool(re.search(r"\bOR\s+REPLACE\b", sql, re.I))

        sql = re.sub(r"\bOR\s+IGNORE\b\s*",  "", sql, flags=re.I)
        sql = re.sub(r"\bOR\s+REPLACE\b\s*", "", sql, flags=re.I)

        # datetime('now') → NOW()
        sql = re.sub(r"datetime\s*\(\s*'now'\s*\)", "NOW()", sql, flags=re.I)
        sql = re.sub(
            r"datetime\s*\(\s*'now'\s*,\s*'([^']+)'\s*\)",
            r"NOW() + INTERVAL '\1'",
            sql, flags=re.I,
        )

        # ? → $1, $2, ...
        n = [0]
        def _rep(_): n[0] += 1; return f"${n[0]}"
        sql = re.sub(r"\?", _rep, sql)

        if (or_ignore or or_replace) and "ON CONFLICT" not in sql.upper():
            sql = sql.rstrip().rstrip(";") + " ON CONFLICT DO NOTHING"

        return sql, tuple(params) if params else ()

    @staticmethod
    def _translate_ddl(sql: str) -> str:
        """Translate SQLite DDL → PostgreSQL DDL."""
        # SQLite INTEGER is 64-bit, PostgreSQL INTEGER is 32-bit.
        # Discord IDs (Snowflakes) require 64-bit (BIGINT).
        sql = re.sub(
            r"\bINTEGER\s+PRIMARY\s+KEY\s+AUTOINCREMENT\b",
            "BIGINT GENERATED ALWAYS AS IDENTITY PRIMARY KEY",
            sql, flags=re.I,
        )
        sql = re.sub(r"\bINTEGER\s+PRIMARY\s+KEY\b", "BIGINT PRIMARY KEY", sql, flags=re.I)
        sql = re.sub(r"\bINTEGER\b", "BIGINT", sql, flags=re.I)
        
        sql = re.sub(r"\bAUTOINCREMENT\b", "", sql, flags=re.I)
        sql = re.sub(r"\bDATETIME\b", "TIMESTAMP", sql, flags=re.I)
        sql = re.sub(r"datetime\s*\(\s*'now'\s*\)", "NOW()", sql, flags=re.I)
        sql = re.sub(r"\bREAL\b", "DOUBLE PRECISION", sql, flags=re.I)
        return sql

    # ── Public interface (matches aiosqlite Connection) ────────────────────

    def execute(self, sql: str, params=()):
        is_ddl = bool(re.match(r"\s*(CREATE|ALTER|DROP|PRAGMA)", sql, re.I))
        if is_ddl:
            translated = self._translate_ddl(sql)
            return _PGExecContext(self._conn, translated, ())
        pg_sql, pg_params = self._translate_dml(sql, params)
        return _PGExecContext(self._conn, pg_sql, pg_params)

    async def executemany(self, sql: str, param_list):
        for params in param_list:
            pg_sql, pg_params = self._translate_dml(sql, params)
            await self._conn.execute(pg_sql, *pg_params)

    async def commit(self):
        pass  # asyncpg autocommits each statement by default


# ── Connection context manager ─────────────────────────────────────────────────

class _PGConnContext:
    """Returned by make_context(pool). Use as `async with ctx as db:`."""

    def __init__(self, pool: "asyncpg.Pool"):
        self._pool = pool
        self._conn: asyncpg.Connection | None = None

    async def __aenter__(self) -> _PGConn:
        self._conn = await self._pool.acquire()
        return _PGConn(self._conn)

    async def __aexit__(self, *_):
        if self._conn:
            await self._pool.release(self._conn)
            self._conn = None


# ── Public API ─────────────────────────────────────────────────────────────────

async def create_pg_pool() -> "asyncpg.Pool":
    """
    Create an asyncpg connection pool from DATABASE_URL.
    Handles the postgres:// → postgresql:// normalization that
    Neon and Supabase sometimes produce.
    """
    if not _ASYNCPG_AVAILABLE:
        raise RuntimeError("asyncpg is not installed; cannot connect to PostgreSQL.")
    url = DATABASE_URL or ""
    if url.startswith("postgres://"):
        url = "postgresql://" + url[11:]
    logger.info("Connecting to PostgreSQL (DATABASE_URL is set)...")
    pool = await asyncpg.create_pool(
        url,
        min_size=1,
        max_size=10,
        statement_cache_size=0,   # required for PgBouncer / Neon pooler
        command_timeout=30,
    )
    logger.info("✓ PostgreSQL pool ready.")
    return pool


def make_context(pool: "asyncpg.Pool") -> _PGConnContext:
    """Return a context manager that yields a _PGConn."""
    return _PGConnContext(pool)
