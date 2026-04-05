"""
XERO Bot — Database Manager
Uses PostgreSQL (asyncpg) when DATABASE_URL is set — data survives all Railway redeploys.
Falls back to SQLite (aiosqlite) for local development.
"""

import os
import aiosqlite
import logging
from utils.db_adapter import DATABASE_URL, create_pg_pool, make_context

logger = logging.getLogger("XERO.Database")


class Database:
    def __init__(self, db_path="data/xero.db"):
        self.db_path = db_path
        self._pool   = None   # asyncpg pool, set in initialize() when DATABASE_URL is set

    async def initialize(self):
        # Prefer PostgreSQL (permanent persistence, no redeploy data loss)
        if DATABASE_URL:
            self._pool = await create_pg_pool()
        async with self._db_context() as db:
            # ── Guild Settings ─────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS guild_settings (
                    guild_id INTEGER PRIMARY KEY,
                    prefix TEXT DEFAULT '/',
                    language TEXT DEFAULT 'en',
                    persona TEXT DEFAULT 'neutral',
                    log_channel_id INTEGER,
                    welcome_channel_id INTEGER,
                    welcome_message TEXT DEFAULT 'Welcome {user} to {server}! You are member #{count}.',
                    welcome_image_url TEXT,
                    farewell_channel_id INTEGER,
                    farewell_message TEXT DEFAULT 'Goodbye {user}, we will miss you!',
                    autorole_id INTEGER,
                    mute_role_id INTEGER,
                    ai_sensitivity TEXT DEFAULT 'medium',
                    verify_role_id INTEGER,
                    verify_message TEXT DEFAULT 'Click the button below to verify!',
                    verify_channel_id INTEGER,
                    verify_tier INTEGER DEFAULT 1,
                    verify_question TEXT DEFAULT 'What is the server code?',
                    verify_answer TEXT,
                    verify_log_channel_id INTEGER,
                    quarantine_role_id INTEGER,
                    ticket_category_id INTEGER,
                    ticket_support_role_id INTEGER,
                    ticket_log_channel_id INTEGER,
                    leveling_enabled INTEGER DEFAULT 1,
                    economy_enabled INTEGER DEFAULT 1,
                    music_enabled INTEGER DEFAULT 1,
                    ai_enabled INTEGER DEFAULT 1,
                    automod_enabled INTEGER DEFAULT 0,
                    timezone TEXT DEFAULT 'UTC',
                    level_up_channel_id INTEGER,
                    unified_image_data TEXT,
                    embed_color TEXT DEFAULT '#5865F2',
                    bot_nickname TEXT
                )
            """)

            # ── Moderation Cases ──────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS mod_cases (
                    case_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    mod_id INTEGER NOT NULL,
                    action TEXT NOT NULL,
                    reason TEXT DEFAULT 'No reason provided',
                    duration INTEGER,
                    timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── Warnings ──────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS warnings (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    mod_id INTEGER NOT NULL,
                    reason TEXT DEFAULT 'No reason provided',
                    type TEXT DEFAULT 'formal',
                    timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── Economy ───────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS economy (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    wallet INTEGER DEFAULT 500,
                    bank INTEGER DEFAULT 0,
                    bank_limit INTEGER DEFAULT 10000,
                    total_earned INTEGER DEFAULT 0,
                    total_spent INTEGER DEFAULT 0,
                    last_daily TIMESTAMP,
                    last_work TIMESTAMP,
                    last_weekly TIMESTAMP,
                    last_rob TIMESTAMP,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)

            # ── Economy Shop ──────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS economy_shop (
                    item_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    description TEXT DEFAULT 'A shop item.',
                    price INTEGER NOT NULL,
                    role_id INTEGER,
                    stock INTEGER DEFAULT -1,
                    emoji TEXT DEFAULT '🛍️'
                )
            """)

            # ── Economy Inventory ─────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS economy_inventory (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    item_name TEXT NOT NULL,
                    quantity INTEGER DEFAULT 1,
                    acquired_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── Levels ────────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS levels (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    xp INTEGER DEFAULT 0,
                    level INTEGER DEFAULT 0,
                    total_xp INTEGER DEFAULT 0,
                    last_msg_timestamp TIMESTAMP,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)

            # ── Level Rewards ─────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS level_rewards (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    level INTEGER NOT NULL,
                    role_id INTEGER NOT NULL,
                    UNIQUE(guild_id, level)
                )
            """)

            # ── Member Profiles (skill graph + personality memory) ──────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS member_profiles (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    skills TEXT DEFAULT '{}',
                    interests TEXT DEFAULT '{}',
                    personality TEXT DEFAULT '{}',
                    xero_knows TEXT DEFAULT '{}',
                    last_updated DATETIME DEFAULT CURRENT_TIMESTAMP,
                    message_sample TEXT,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS skill_observations (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    skill TEXT NOT NULL,
                    evidence TEXT,
                    confidence REAL DEFAULT 0.5,
                    observed_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── Tickets ───────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS tickets (
                    ticket_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    status TEXT DEFAULT 'open',
                    topic TEXT DEFAULT 'General Support',
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                    closed_at DATETIME,
                    closed_by INTEGER,
                    claimed_by INTEGER,
                    rating INTEGER,
                    rating_feedback TEXT,
                    message_count INTEGER DEFAULT 0,
                    ai_summary TEXT,
                    log_message_id INTEGER
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS ticket_events (
                    event_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ticket_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    event_type TEXT NOT NULL,
                    detail TEXT,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── Giveaways ─────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS giveaways (
                    giveaway_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    message_id INTEGER,
                    prize TEXT NOT NULL,
                    winners_count INTEGER DEFAULT 1,
                    end_time DATETIME NOT NULL,
                    created_by INTEGER,
                    ended INTEGER DEFAULT 0,
                    paused INTEGER DEFAULT 0,
                    requirements TEXT
                )
            """)

            await db.execute("""
                CREATE TABLE IF NOT EXISTS giveaway_participants (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    giveaway_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    UNIQUE(giveaway_id, user_id)
                )
            """)

             # ── Announcements ─────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS announcements (
                    announcement_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    title TEXT NOT NULL,
                    message TEXT NOT NULL,
                    scheduled_time DATETIME,
                    created_by INTEGER,
                    sent INTEGER DEFAULT 0
                )
            """)

            # ── Aegis Protocol (Verification & Risk) ────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS aegis_quarantine (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    risk_score INTEGER DEFAULT 0,
                    risk_factors TEXT,
                    status TEXT DEFAULT 'pending',
                    appeal_message TEXT,
                    joined_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS global_risk_cache (
                    user_id INTEGER PRIMARY KEY,
                    risk_score INTEGER DEFAULT 0,
                    cross_server_bans INTEGER DEFAULT 0,
                    last_updated DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── Verification ──────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS verification_config (
                    guild_id INTEGER PRIMARY KEY,
                    channel_id INTEGER,
                    role_id INTEGER,
                    message TEXT DEFAULT 'Click the button below to verify!'
                )
            """)

            await db.execute("""
                CREATE TABLE IF NOT EXISTS user_verifications (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    verified_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)

            # ── Logging Ignores ───────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS log_ignored_channels (
                    guild_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    PRIMARY KEY (guild_id, channel_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS log_ignored_roles (
                    guild_id INTEGER NOT NULL,
                    role_id INTEGER NOT NULL,
                    PRIMARY KEY (guild_id, role_id)
                )
            """)

            # ── Server Backups ────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS server_backups (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    backup_name TEXT DEFAULT 'Backup',
                    backup_data TEXT NOT NULL,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── AutoMod ───────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS automod_config (
                    guild_id INTEGER PRIMARY KEY,
                    enabled INTEGER DEFAULT 0,
                    anti_spam INTEGER DEFAULT 0,
                    anti_links INTEGER DEFAULT 0,
                    anti_caps INTEGER DEFAULT 0,
                    anti_profanity INTEGER DEFAULT 0,
                    max_mentions INTEGER DEFAULT 5,
                    spam_threshold INTEGER DEFAULT 5,
                    log_channel_id INTEGER,
                    action TEXT DEFAULT 'delete'
                )
            """)

            await db.execute("""
                CREATE TABLE IF NOT EXISTS automod_filters (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    filter_type TEXT NOT NULL,
                    value TEXT NOT NULL
                )
            """)

            # ── User Stats (Leaderboard) ──────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS user_stats (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    commands_used INTEGER DEFAULT 0,
                    messages_sent INTEGER DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)

            # ── Reminders ─────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS reminders (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    message TEXT NOT NULL,
                    remind_at DATETIME NOT NULL,
                    sent INTEGER DEFAULT 0
                )
            """)

            # ── AFK ───────────────────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS afk_users (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    reason TEXT DEFAULT 'AFK',
                    set_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)

            await db.commit()
        logger.info("✓ All database tables ready.")
        await self.ensure_extra_tables()

    # ── Guild Settings ────────────────────────────────────────────────────

    async def get_guild_settings(self, guild_id: int) -> dict:
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            try:
                async with db.execute("SELECT * FROM guild_settings WHERE guild_id=?", (guild_id,)) as c:
                    row = await c.fetchone()
                if row: return dict(row)
            except Exception as e:
                logger.warning(f"Error fetching guild settings for {guild_id}: {e}")
            
            # If not found, create and return default
            await db.execute("INSERT INTO guild_settings (guild_id) VALUES (?) ON CONFLICT (guild_id) DO NOTHING", (guild_id,))
            await db.commit()
            async with db.execute("SELECT * FROM guild_settings WHERE guild_id=?", (guild_id,)) as c:
                row = await c.fetchone()
            return dict(row) if row else {}

    async def update_guild_setting(self, guild_id: int, key: str, value):
        async with self._db_context() as db:
            # Atomic upsert for PostgreSQL/SQLite
            await db.execute(f"""
                INSERT INTO guild_settings (guild_id, {key}) VALUES (?, ?)
                ON CONFLICT (guild_id) DO UPDATE SET {key} = EXCLUDED.{key}
            """, (guild_id, value))
            await db.commit()
        
        # Trigger immediate backup to ensure persistence across redeploys
        from main import bot_instance
        if bot_instance:
            from utils.db_backup import send_backup
            import asyncio
            # Use a small delay to debounce multiple rapid changes
            async def delayed_backup():
                await asyncio.sleep(5)
                await send_backup(bot_instance, triggered_by=f"config_change_{key}")
            asyncio.create_task(delayed_backup())

    async def create_guild_settings(self, guild_id: int):
        async with self._db_context() as db:
            await db.execute("INSERT OR IGNORE INTO guild_settings (guild_id) VALUES (?)", (guild_id,))
            await db.commit()
        
        # Trigger backup for new guild
        from main import bot_instance
        if bot_instance:
            from utils.db_backup import send_backup
            import asyncio
            asyncio.create_task(send_backup(bot_instance, triggered_by=f"new_guild_{guild_id}"))

    # ── Economy ───────────────────────────────────────────────────────────

    async def get_economy(self, user_id: int, guild_id: int) -> dict:
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM economy WHERE user_id=? AND guild_id=?", (user_id, guild_id)) as c:
                row = await c.fetchone()
            if row:
                return dict(row)
            await db.execute("INSERT INTO economy (user_id, guild_id) VALUES (?,?)", (user_id, guild_id))
            await db.commit()
            return {"user_id": user_id, "guild_id": guild_id, "wallet": 500, "bank": 0,
                    "bank_limit": 10000, "total_earned": 0, "total_spent": 0,
                    "last_daily": None, "last_work": None, "last_weekly": None, "last_rob": None}

    async def update_economy(self, user_id: int, guild_id: int, wallet_delta=0, bank_delta=0, earned_delta=0, spent_delta=0):
        async with self._db_context() as db:
            await db.execute("INSERT OR IGNORE INTO economy (user_id, guild_id) VALUES (?,?)", (user_id, guild_id))
            if wallet_delta:
                await db.execute("UPDATE economy SET wallet=MAX(0,wallet+?) WHERE user_id=? AND guild_id=?",
                                  (wallet_delta, user_id, guild_id))
            if bank_delta:
                await db.execute("UPDATE economy SET bank=MAX(0,bank+?) WHERE user_id=? AND guild_id=?",
                                  (bank_delta, user_id, guild_id))
            if earned_delta > 0:
                await db.execute("UPDATE economy SET total_earned=total_earned+? WHERE user_id=? AND guild_id=?",
                                  (earned_delta, user_id, guild_id))
            if spent_delta > 0:
                await db.execute("UPDATE economy SET total_spent=total_spent+? WHERE user_id=? AND guild_id=?",
                                  (spent_delta, user_id, guild_id))
            await db.commit()

    async def set_economy_timestamp(self, user_id: int, guild_id: int, field: str, value: str):
        async with self._db_context() as db:
            await db.execute(f"UPDATE economy SET {field}=? WHERE user_id=? AND guild_id=?", (value, user_id, guild_id))
            await db.commit()

    async def get_economy_leaderboard(self, guild_id: int, limit=10):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT user_id, wallet, bank, wallet+bank as total FROM economy WHERE guild_id=? ORDER BY total DESC LIMIT ?",
                (guild_id, limit)
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    # ── Levels ────────────────────────────────────────────────────────────

    async def get_level(self, user_id: int, guild_id: int) -> dict:
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM levels WHERE user_id=? AND guild_id=?", (user_id, guild_id)) as c:
                row = await c.fetchone()
            if row:
                return dict(row)
            await db.execute("INSERT INTO levels (user_id, guild_id) VALUES (?,?)", (user_id, guild_id))
            await db.commit()
            return {"user_id": user_id, "guild_id": guild_id, "xp": 0, "level": 0, "total_xp": 0, "last_msg_timestamp": None}

    @staticmethod
    def xp_for_level(level: int) -> int:
        """
        XP needed to go from level N to level N+1.
        Exponential curve — gets significantly harder each level.
        Level 1→2:   ~450 XP   |  Level 5→6:   ~4,600 XP
        Level 10→11: ~16,000 XP |  Level 25→26: ~120,000 XP
        """
        return int(100 * (level + 1) ** 2.2)

    @staticmethod
    def xp_multiplier(level: int, is_bot_command: bool = False) -> float:
        """
        Passive (messaging):    level 0=1.0x, level 2=1.1x, +0.05x per level (cap 3.0x)
        Bot command bonus:      always 2x on top of passive multiplier
        Examples:
          Level 1, message:     1.0x
          Level 2, message:     1.1x
          Level 2, bot command: 2.1x
          Level 10, message:    1.5x
          Level 10, bot command:2.5x
        """
        passive = min(1.0 + max(0, level - 1) * 0.05, 3.0)
        if is_bot_command:
            return passive + 1.0
        return passive

    async def update_xp(self, user_id: int, guild_id: int, xp_gain: int, is_bot_command: bool = False):
        """Returns (leveled_up: bool, new_level: int)"""
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            await db.execute("INSERT OR IGNORE INTO levels (user_id, guild_id) VALUES (?,?)", (user_id, guild_id))
            async with db.execute("SELECT xp, level FROM levels WHERE user_id=? AND guild_id=?", (user_id, guild_id)) as c:
                row = await c.fetchone()
            current_level = row["level"]
            # Apply level multiplier
            multiplier  = self.xp_multiplier(current_level, is_bot_command)
            actual_gain = max(1, int(xp_gain * multiplier))
            current_xp  = row["xp"] + actual_gain
            leveled_up  = False
            xp_needed   = self.xp_for_level(current_level)
            while current_xp >= xp_needed:
                current_xp -= xp_needed
                current_level += 1
                leveled_up = True
                xp_needed = self.xp_for_level(current_level)
            await db.execute(
                "UPDATE levels SET xp=?, level=?, total_xp=total_xp+? WHERE user_id=? AND guild_id=?",
                (current_xp, current_level, actual_gain, user_id, guild_id)
            )
            await db.commit()
            return leveled_up, current_level

    async def get_level_leaderboard(self, guild_id: int, limit=10):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT user_id, level, total_xp FROM levels WHERE guild_id=? ORDER BY total_xp DESC LIMIT ?",
                (guild_id, limit)
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    async def set_user_xp(self, user_id: int, guild_id: int, xp: int, level: int):
        async with self._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO levels (user_id, guild_id, xp, level, total_xp) VALUES (?,?,?,?,?)",
                (user_id, guild_id, xp, level, xp)
            )
            await db.commit()

    # ── Moderation ────────────────────────────────────────────────────────

    async def add_mod_case(self, guild_id, user_id, mod_id, action, reason, duration=None) -> int:
        async with self._db_context() as db:
            async with db.execute(
                "INSERT INTO mod_cases (guild_id, user_id, mod_id, action, reason, duration) VALUES (?,?,?,?,?,?)",
                (guild_id, user_id, mod_id, action, reason, duration)
            ) as c:
                case_id = c.lastrowid
            await db.commit()
            return case_id

    async def get_mod_cases(self, guild_id, user_id=None, limit=10):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            if user_id:
                async with db.execute(
                    "SELECT * FROM mod_cases WHERE guild_id=? AND user_id=? ORDER BY timestamp DESC LIMIT ?",
                    (guild_id, user_id, limit)
                ) as c:
                    return [dict(r) for r in await c.fetchall()]
            async with db.execute(
                "SELECT * FROM mod_cases WHERE guild_id=? ORDER BY timestamp DESC LIMIT ?",
                (guild_id, limit)
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    async def add_warning(self, guild_id, user_id, mod_id, reason, warn_type="formal") -> int:
        async with self._db_context() as db:
            await db.execute(
                "INSERT INTO warnings (guild_id, user_id, mod_id, reason, type) VALUES (?,?,?,?,?)",
                (guild_id, user_id, mod_id, reason, warn_type)
            )
            await db.commit()
            async with db.execute(
                "SELECT COUNT(*) FROM warnings WHERE guild_id=? AND user_id=? AND type='formal'", (guild_id, user_id)
            ) as c:
                row = await c.fetchone()
                return row[0]

    async def get_soft_warnings_count(self, guild_id, user_id) -> int:
        async with self._db_context() as db:
            async with db.execute(
                "SELECT COUNT(*) FROM warnings WHERE guild_id=? AND user_id=? AND type='soft'", (guild_id, user_id)
            ) as c:
                row = await c.fetchone()
                return row[0] if row else 0

    async def get_warnings(self, guild_id, user_id):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM warnings WHERE guild_id=? AND user_id=? ORDER BY timestamp DESC",
                (guild_id, user_id)
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    async def clear_warnings(self, guild_id, user_id):
        async with self._db_context() as db:
            await db.execute("DELETE FROM warnings WHERE guild_id=? AND user_id=?", (guild_id, user_id))
            await db.commit()

    # ── Stats ─────────────────────────────────────────────────────────────

    async def increment_stat(self, user_id: int, guild_id: int, stat="commands_used"):
        async with self._db_context() as db:
            await db.execute("INSERT OR IGNORE INTO user_stats (user_id, guild_id) VALUES (?,?)", (user_id, guild_id))
            await db.execute(
                f"UPDATE user_stats SET {stat}={stat}+1 WHERE user_id=? AND guild_id=?",
                (user_id, guild_id)
            )
            await db.commit()

    async def get_stats_leaderboard(self, guild_id: int, limit=10):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT user_id, commands_used, messages_sent FROM user_stats WHERE guild_id=? ORDER BY commands_used DESC LIMIT ?",
                (guild_id, limit)
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    async def get_user_stats(self, user_id: int, guild_id: int) -> dict:
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM user_stats WHERE user_id=? AND guild_id=?", (user_id, guild_id)
            ) as c:
                row = await c.fetchone()
            return dict(row) if row else {"user_id": user_id, "guild_id": guild_id, "commands_used": 0, "messages_sent": 0}

    # ── Level Rewards ─────────────────────────────────────────────────────

    async def add_level_reward(self, guild_id: int, level: int, role_id: int):
        async with self._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO level_rewards (guild_id, level, role_id) VALUES (?,?,?)",
                (guild_id, level, role_id)
            )
            await db.commit()

    async def get_level_rewards(self, guild_id: int):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM level_rewards WHERE guild_id=? ORDER BY level ASC", (guild_id,)
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    async def remove_level_reward(self, guild_id: int, level: int):
        async with self._db_context() as db:
            await db.execute("DELETE FROM level_rewards WHERE guild_id=? AND level=?", (guild_id, level))
            await db.commit()

    # ── AFK ───────────────────────────────────────────────────────────────

    async def set_afk(self, user_id: int, guild_id: int, reason: str):
        async with self._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO afk_users (user_id, guild_id, reason) VALUES (?,?,?)",
                (user_id, guild_id, reason)
            )
            await db.commit()

    async def get_afk(self, user_id: int, guild_id: int):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM afk_users WHERE user_id=? AND guild_id=?", (user_id, guild_id)
            ) as c:
                row = await c.fetchone()
            return dict(row) if row else None

    async def remove_afk(self, user_id: int, guild_id: int):
        async with self._db_context() as db:
            await db.execute("DELETE FROM afk_users WHERE user_id=? AND guild_id=?", (user_id, guild_id))
            await db.commit()

    # ── Reminders ─────────────────────────────────────────────────────────

    async def add_reminder(self, user_id: int, channel_id: int, message: str, remind_at: str) -> int:
        async with self._db_context() as db:
            async with db.execute(
                "INSERT INTO reminders (user_id, channel_id, message, remind_at) VALUES (?,?,?,?)",
                (user_id, channel_id, message, remind_at)
            ) as c:
                rid = c.lastrowid
            await db.commit()
            return rid

    async def get_due_reminders(self):
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM reminders WHERE sent=0 AND remind_at <= datetime('now')"
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    async def mark_reminder_sent(self, reminder_id: int):
        async with self._db_context() as db:
            await db.execute("UPDATE reminders SET sent=1 WHERE id=?", (reminder_id,))
            await db.commit()

    async def ensure_extra_tables(self):
        """Ensure all new tables exist."""
        async with self._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS birthdays (
                    user_id INTEGER NOT NULL, guild_id INTEGER NOT NULL,
                    day INTEGER NOT NULL, month INTEGER NOT NULL,
                    year INTEGER, announced_year INTEGER DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS suggestions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL, user_id INTEGER NOT NULL,
                    channel_id INTEGER, message_id INTEGER,
                    title TEXT NOT NULL, description TEXT NOT NULL,
                    status TEXT DEFAULT 'pending',
                    staff_response TEXT, reviewed_by INTEGER,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS reaction_role_panels (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL, channel_id INTEGER NOT NULL,
                    message_id INTEGER, title TEXT NOT NULL,
                    description TEXT, roles_data TEXT DEFAULT '[]'
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS starboard_config (
                    guild_id INTEGER PRIMARY KEY, channel_id INTEGER NOT NULL,
                    threshold INTEGER DEFAULT 3, enabled INTEGER DEFAULT 1
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS starboard_messages (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL, original_id INTEGER UNIQUE,
                    starboard_id INTEGER, channel_id INTEGER
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS counting_config (
                    guild_id INTEGER NOT NULL, channel_id INTEGER NOT NULL,
                    current INTEGER DEFAULT 0, last_user_id INTEGER,
                    high_score INTEGER DEFAULT 0, enabled INTEGER DEFAULT 1,
                    PRIMARY KEY (guild_id, channel_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS confessions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL, user_id INTEGER NOT NULL,
                    message TEXT NOT NULL,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            # Extra guild settings columns
            for col_def in [
                "birthday_channel_id INTEGER",
                "birthday_role_id INTEGER",
                "suggestion_channel_id INTEGER",
                "confession_channel_id INTEGER",
                "welcome_use_banner INTEGER DEFAULT 0",
                "welcome_image_enabled INTEGER DEFAULT 0",
                "automod_max_mentions INTEGER DEFAULT 5",
                "automod_max_lines INTEGER DEFAULT 20",
                "automod_spam_limit INTEGER DEFAULT 5",
                "automod_invite_action TEXT DEFAULT 'delete'",
                "automod_log_channel_id INTEGER",
                "personality_enabled INTEGER DEFAULT 1",
                "milestone_channel_id INTEGER",
                "raid_protection INTEGER DEFAULT 1",
                "raid_threshold INTEGER DEFAULT 5",
                "raid_window INTEGER DEFAULT 30",
                "auto_escalate INTEGER DEFAULT 1",
                "anti_nuke_enabled INTEGER DEFAULT 0",
                "anti_nuke_threshold INTEGER DEFAULT 3",
                "min_account_age_days INTEGER DEFAULT 0",
                "account_age_action TEXT DEFAULT 'kick_dm'",
                "link_filter_enabled INTEGER DEFAULT 0",
                "role_restore_enabled INTEGER DEFAULT 0",
                "message_log_channel_id INTEGER",
                "member_log_channel_id INTEGER",
                "server_log_channel_id INTEGER",
                "voice_log_channel_id INTEGER",
                "bump_role_id INTEGER",
                "voice_xp_enabled INTEGER DEFAULT 0",
                "voice_xp_rate INTEGER DEFAULT 5",
                "levelup_dm_enabled INTEGER DEFAULT 0",
                "levelup_dm_message TEXT",
                "webhook_protection_enabled INTEGER DEFAULT 0",
                "welcome_dm_enabled INTEGER DEFAULT 0",
                "welcome_dm_message TEXT",
                "welcome_dm_image_url TEXT",
                "welcome_card_show_name INTEGER DEFAULT 1",
                "welcome_card_show_avatar INTEGER DEFAULT 1",
                "welcome_card_show_count INTEGER DEFAULT 1",
                "welcome_card_text_color TEXT DEFAULT '#FFFFFF'",
                "welcome_card_text_pos TEXT DEFAULT 'bottom_left'",
                "welcome_card_overlay TEXT DEFAULT 'gradient'",
                "welcome_card_font_size INTEGER DEFAULT 52",
                "welcome_card_image_data TEXT",
                "aimod_enabled INTEGER DEFAULT 0",
                "aimod_threshold TEXT DEFAULT '0.7'",
                "aimod_action TEXT DEFAULT 'delete'",
                "aimod_log_channel_id INTEGER",
                "temp_voice_enabled INTEGER DEFAULT 0",
                "stock_enabled INTEGER DEFAULT 1",
                "verify_methods TEXT DEFAULT 'math'",
                "highlight_enabled INTEGER DEFAULT 0",
                "highlight_channel_id INTEGER",
            ]:
                try:
                    await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col_def}")
                except Exception:
                    pass  # Column already exists
            await db.commit()
        logger.info("✓ Extra tables and columns ready.")


    async def initialize_advanced(self):
        """Initialize advanced feature tables."""
        async with self._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS suggestions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    message_id INTEGER,
                    title TEXT NOT NULL,
                    description TEXT NOT NULL,
                    status TEXT DEFAULT 'pending',
                    staff_response TEXT,
                    reviewed_by INTEGER,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS birthdays (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    day INTEGER NOT NULL,
                    month INTEGER NOT NULL,
                    year INTEGER,
                    announced_year INTEGER DEFAULT 0,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS custom_commands (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    response TEXT NOT NULL,
                    embed_title TEXT,
                    embed_color TEXT DEFAULT 'blue',
                    role_id INTEGER,
                    uses INTEGER DEFAULT 0,
                    created_by INTEGER,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                    UNIQUE(guild_id, name)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS temp_voice_config (
                    guild_id INTEGER PRIMARY KEY,
                    trigger_channel_id INTEGER NOT NULL,
                    category_id INTEGER,
                    default_name TEXT DEFAULT '{user} Channel',
                    default_limit INTEGER DEFAULT 0
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS temp_voice_channels (
                    channel_id INTEGER PRIMARY KEY,
                    guild_id INTEGER NOT NULL,
                    owner_id INTEGER NOT NULL,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS scheduled_messages (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    message TEXT NOT NULL,
                    embed_title TEXT,
                    send_at DATETIME NOT NULL,
                    repeat_hours INTEGER DEFAULT 0,
                    sent INTEGER DEFAULT 0,
                    created_by INTEGER
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS aimod_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    message TEXT NOT NULL,
                    toxicity_score REAL,
                    action_taken TEXT,
                    timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            # Extra columns
            for col_def in [
                "aimod_enabled INTEGER DEFAULT 0",
                "aimod_threshold TEXT DEFAULT '0.7'",
                "temp_voice_enabled INTEGER DEFAULT 0",
                "welcome_image_enabled INTEGER DEFAULT 0",
                "aimod_action TEXT DEFAULT 'delete'",
                "aimod_log_channel_id INTEGER",
            ]:
                try:
                    await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col_def}")
                except Exception:
                    pass
            await db.commit()
        logger.info("✓ Advanced tables ready.")

    async def initialize_xero_tables(self):
        """New tables for XERO v3 features."""
        async with self._db_context() as db:
            # Economy streaks
            await db.execute("""
                CREATE TABLE IF NOT EXISTS economy_streaks (
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    daily_streak INTEGER DEFAULT 0,
                    best_streak INTEGER DEFAULT 0,
                    last_daily_date TEXT,
                    PRIMARY KEY (user_id, guild_id)
                )
            """)
            # Stocks
            await db.execute("""
                CREATE TABLE IF NOT EXISTS stocks (
                    symbol TEXT PRIMARY KEY,
                    name TEXT NOT NULL,
                    price INTEGER NOT NULL,
                    prev_price INTEGER NOT NULL,
                    volatility REAL DEFAULT 0.1,
                    last_updated DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            # Stock portfolios
            await db.execute("""
                CREATE TABLE IF NOT EXISTS stock_portfolio (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    symbol TEXT NOT NULL,
                    shares INTEGER NOT NULL,
                    avg_buy_price INTEGER NOT NULL,
                    UNIQUE(user_id, guild_id, symbol)
                )
            """)
            # Crafting recipes
            await db.execute("""
                CREATE TABLE IF NOT EXISTS craft_recipes (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    result_item TEXT NOT NULL,
                    ingredient1 TEXT NOT NULL,
                    ingredient2 TEXT NOT NULL,
                    ingredient3 TEXT,
                    result_value INTEGER DEFAULT 0
                )
            """)
            # Active heists
            await db.execute("""
                CREATE TABLE IF NOT EXISTS heists (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    leader_id INTEGER NOT NULL,
                    target TEXT NOT NULL,
                    potential INTEGER NOT NULL,
                    status TEXT DEFAULT 'recruiting',
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS heist_participants (
                    heist_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    PRIMARY KEY (heist_id, user_id)
                )
            """)
            # Raid log
            await db.execute("""
                CREATE TABLE IF NOT EXISTS raid_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    join_count INTEGER NOT NULL,
                    action_taken TEXT NOT NULL,
                    timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            # Server health cache
            await db.execute("""
                CREATE TABLE IF NOT EXISTS health_cache (
                    guild_id INTEGER PRIMARY KEY,
                    score INTEGER NOT NULL,
                    analysis TEXT,
                    last_checked DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            # Personality event log (avoid repeating same message)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS personality_log (
                    guild_id INTEGER NOT NULL,
                    event_type TEXT NOT NULL,
                    last_fired DATETIME DEFAULT CURRENT_TIMESTAMP,
                    PRIMARY KEY (guild_id, event_type)
                )
            """)
            # Add new columns to guild_settings safely
            new_cols = [
                "birthday_channel_id INTEGER",
                "raid_protection INTEGER DEFAULT 1",
                "raid_threshold INTEGER DEFAULT 5",
                "raid_window INTEGER DEFAULT 30",
                "auto_escalate INTEGER DEFAULT 1",
                "stock_enabled INTEGER DEFAULT 1",
                "personality_enabled INTEGER DEFAULT 1",
                "milestone_channel_id INTEGER",
            ]
            for col in new_cols:
                try:
                    await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col}")
                except Exception:
                    pass
            # Seed default stocks if empty
            async with db.execute("SELECT COUNT(*) FROM stocks") as c:
                count = (await c.fetchone())[0]
            if count == 0:
                default_stocks = [
                    ("XERO", "XERO Technologies",       1000, 1000, 0.12),
                    ("DISC", "Discord Inc.",             850,  850,  0.08),
                    ("NVDA", "NVIDIA Corporation",       950,  950,  0.15),
                    ("GOOG", "Alphabet Inc.",            1200, 1200, 0.07),
                    ("MEME", "Meme Finance Corp",        200,  200,  0.35),
                    ("DOGE", "Doge Capital",             50,   50,   0.45),
                    ("MOON", "Lunar Industries",         600,  600,  0.20),
                    ("XBOT", "XERO Bot Holdings",        750,  750,  0.10),
                ]
                await db.executemany(
                    "INSERT INTO stocks (symbol,name,price,prev_price,volatility) VALUES (?,?,?,?,?)",
                    default_stocks
                )
            await db.commit()
        logger.info("✓ XERO v3 tables ready.")

    async def initialize_v4_tables(self):
        """XERO v4 — new feature tables."""
        async with self._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS member_roles (
                    user_id   INTEGER NOT NULL,
                    guild_id  INTEGER NOT NULL,
                    role_ids  TEXT NOT NULL,
                    saved_at  DATETIME DEFAULT CURRENT_TIMESTAMP,
                    PRIMARY KEY(user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS economy_transactions (
                    id          INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id     INTEGER NOT NULL,
                    guild_id    INTEGER NOT NULL,
                    amount      INTEGER NOT NULL,
                    type        TEXT NOT NULL,
                    description TEXT,
                    timestamp   DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS reputation (
                    user_id    INTEGER NOT NULL,
                    guild_id   INTEGER NOT NULL,
                    rep        INTEGER DEFAULT 0,
                    last_given TEXT,
                    PRIMARY KEY(user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS marriages (
                    user1_id   INTEGER NOT NULL,
                    user2_id   INTEGER NOT NULL,
                    guild_id   INTEGER NOT NULL,
                    married_at TEXT,
                    PRIMARY KEY(user1_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS user_timezones (
                    user_id  INTEGER PRIMARY KEY,
                    timezone TEXT NOT NULL
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS weekly_claims (
                    user_id    INTEGER NOT NULL,
                    guild_id   INTEGER NOT NULL,
                    last_claim TEXT,
                    PRIMARY KEY(user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS stats_channels (
                    guild_id   INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    stat_type  TEXT NOT NULL,
                    PRIMARY KEY(guild_id, stat_type)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS bump_reminders (
                    guild_id   INTEGER PRIMARY KEY,
                    channel_id INTEGER NOT NULL,
                    enabled    INTEGER DEFAULT 1,
                    next_bump  DATETIME
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS allowed_domains (
                    guild_id INTEGER NOT NULL,
                    domain   TEXT NOT NULL,
                    PRIMARY KEY(guild_id, domain)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS xp_blacklist (
                    guild_id   INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    PRIMARY KEY(guild_id, channel_id)
                )
            """)
            # New guild_settings columns
            new_cols = [
                "anti_nuke_enabled INTEGER DEFAULT 0",
                "anti_nuke_threshold INTEGER DEFAULT 3",
                "min_account_age_days INTEGER DEFAULT 0",
                "account_age_action TEXT DEFAULT 'kick_dm'",
                "link_filter_enabled INTEGER DEFAULT 0",
                "role_restore_enabled INTEGER DEFAULT 0",
                "message_log_channel_id INTEGER",
                "bump_role_id INTEGER",
                "suggestion_channel_id INTEGER",
            ]
            for col in new_cols:
                try:
                    await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col}")
                except Exception:
                    pass
            await db.execute("CREATE TABLE IF NOT EXISTS xp_role_multipliers (guild_id INTEGER,role_id INTEGER,multiplier REAL,PRIMARY KEY(guild_id,role_id))")
            # ── AutoMod v2 columns ──────────────────────────────────────────
            automod_v2_cols = [
                "anti_caps INTEGER DEFAULT 0",
                "anti_emoji_spam INTEGER DEFAULT 0",
                "anti_invite INTEGER DEFAULT 0",
                "anti_new_account INTEGER DEFAULT 0",
                "invite_action TEXT DEFAULT 'delete'",
                "new_account_mute_minutes INTEGER DEFAULT 10",
            ]
            for col in automod_v2_cols:
                try: await db.execute(f"ALTER TABLE automod_config ADD COLUMN {col}")
                except Exception: pass

            # ── Automod strikes per user ──────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS automod_strikes (
                    user_id   INTEGER NOT NULL,
                    guild_id  INTEGER NOT NULL,
                    strikes   INTEGER DEFAULT 0,
                    last_strike DATETIME DEFAULT CURRENT_TIMESTAMP,
                    PRIMARY KEY(user_id, guild_id)
                )
            """)

            # ── Alt account / join history ────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS member_join_history (
                    user_id   INTEGER NOT NULL,
                    guild_id  INTEGER NOT NULL,
                    joined_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            # ── Security v2 columns ────────────────────────────────────────
            security_v2_cols = [
                "raid_mode_enabled INTEGER DEFAULT 0",
                "raid_mode_until DATETIME",
                "raid_mode_min_age_days INTEGER DEFAULT 7",
                "bot_protection_enabled INTEGER DEFAULT 0",
                "webhook_protection_enabled INTEGER DEFAULT 1",
                "perm_watchdog_enabled INTEGER DEFAULT 1",
            ]
            for col in security_v2_cols:
                try: await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col}")
                except Exception: pass

            # ── Anti-nuke audit log ────────────────────────────────────────
            await db.execute("""
                CREATE TABLE IF NOT EXISTS antinuke_log (
                    id        INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id  INTEGER NOT NULL,
                    user_id   INTEGER NOT NULL,
                    action    TEXT NOT NULL,
                    count     INTEGER DEFAULT 1,
                    triggered_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )
            """)

            new_v4_cols = [
                "voice_xp_enabled INTEGER DEFAULT 0",
                "voice_xp_rate INTEGER DEFAULT 5",
                "levelup_dm_enabled INTEGER DEFAULT 0",
                "levelup_dm_message TEXT",
                "webhook_protection_enabled INTEGER DEFAULT 0",
                "message_log_channel_id INTEGER",
                "member_log_channel_id INTEGER",
                "server_log_channel_id INTEGER",
                "voice_log_channel_id INTEGER",
                "welcome_dm_enabled INTEGER DEFAULT 0",
                "welcome_dm_message TEXT",
                "welcome_dm_image_url TEXT",
                "welcome_card_show_name INTEGER DEFAULT 1",
                "welcome_card_show_avatar INTEGER DEFAULT 1",
                "welcome_card_show_count INTEGER DEFAULT 1",
                "welcome_card_text_color TEXT DEFAULT '#FFFFFF'",
                "welcome_card_text_pos TEXT DEFAULT 'bottom_left'",
                "welcome_card_overlay TEXT DEFAULT 'gradient'",
                "welcome_card_font_size INTEGER DEFAULT 52",
                "welcome_card_image_data TEXT",
            ]
            for col in new_v4_cols:
                try: await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col}")
                except Exception: pass
            await db.commit()
        logger.info("\u2713 XERO v4 tables ready.")


    # ── Streak helpers ────────────────────────────────────────────────────

    async def get_streak(self, user_id: int, guild_id: int) -> dict:
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM economy_streaks WHERE user_id=? AND guild_id=?",
                (user_id, guild_id)
            ) as c:
                row = await c.fetchone()
            if row:
                return dict(row)
            await db.execute(
                "INSERT OR IGNORE INTO economy_streaks (user_id, guild_id) VALUES (?,?)",
                (user_id, guild_id)
            )
            await db.commit()
            return {"user_id": user_id, "guild_id": guild_id,
                    "daily_streak": 0, "best_streak": 0, "last_daily_date": None}

    async def update_streak(self, user_id: int, guild_id: int, new_streak: int, date_str: str):
        async with self._db_context() as db:
            await db.execute("""
                INSERT INTO economy_streaks (user_id, guild_id, daily_streak, best_streak, last_daily_date)
                VALUES (?,?,?,?,?)
                ON CONFLICT(user_id,guild_id) DO UPDATE SET
                    daily_streak=?,
                    best_streak=MAX(best_streak,?),
                    last_daily_date=?
            """, (user_id, guild_id, new_streak, new_streak, date_str,
                  new_streak, new_streak, date_str))
            await db.commit()

    # ── Stock helpers ─────────────────────────────────────────────────────

    async def get_stocks(self) -> list:
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM stocks ORDER BY symbol") as c:
                return [dict(r) for r in await c.fetchall()]

    async def update_stock_price(self, symbol: str, new_price: int, prev_price: int):
        async with self._db_context() as db:
            await db.execute(
                "UPDATE stocks SET price=?, prev_price=?, last_updated=datetime('now') WHERE symbol=?",
                (max(1, new_price), prev_price, symbol)
            )
            await db.commit()

    async def get_portfolio(self, user_id: int, guild_id: int) -> list:
        async with self._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT p.*, s.price, s.name FROM stock_portfolio p JOIN stocks s ON p.symbol=s.symbol WHERE p.user_id=? AND p.guild_id=?",
                (user_id, guild_id)
            ) as c:
                return [dict(r) for r in await c.fetchall()]

    async def buy_stock(self, user_id: int, guild_id: int, symbol: str, shares: int, price: int):
        async with self._db_context() as db:
            async with db.execute(
                "SELECT shares, avg_buy_price FROM stock_portfolio WHERE user_id=? AND guild_id=? AND symbol=?",
                (user_id, guild_id, symbol)
            ) as c:
                existing = await c.fetchone()
            if existing:
                total_shares = existing[0] + shares
                new_avg = (existing[0] * existing[1] + shares * price) // total_shares
                await db.execute(
                    "UPDATE stock_portfolio SET shares=?, avg_buy_price=? WHERE user_id=? AND guild_id=? AND symbol=?",
                    (total_shares, new_avg, user_id, guild_id, symbol)
                )
            else:
                await db.execute(
                    "INSERT INTO stock_portfolio (user_id,guild_id,symbol,shares,avg_buy_price) VALUES (?,?,?,?,?)",
                    (user_id, guild_id, symbol, shares, price)
                )
            await db.commit()

    async def sell_stock(self, user_id: int, guild_id: int, symbol: str, shares: int):
        async with self._db_context() as db:
            async with db.execute(
                "SELECT shares FROM stock_portfolio WHERE user_id=? AND guild_id=? AND symbol=?",
                (user_id, guild_id, symbol)
            ) as c:
                row = await c.fetchone()
            if not row or row[0] < shares:
                return False
            new_shares = row[0] - shares
            if new_shares == 0:
                await db.execute(
                    "DELETE FROM stock_portfolio WHERE user_id=? AND guild_id=? AND symbol=?",
                    (user_id, guild_id, symbol)
                )
            else:
                await db.execute(
                    "UPDATE stock_portfolio SET shares=? WHERE user_id=? AND guild_id=? AND symbol=?",
                    (new_shares, user_id, guild_id, symbol)
                )
            await db.commit()
            return True

    def _db_context(self):
        """Returns the appropriate database connection context."""
        if self._pool:
            return make_context(self._pool)
        return aiosqlite.connect(self.db_path)
