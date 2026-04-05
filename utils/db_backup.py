"""
XERO Bot — Automatic Database Backup & Restore
===============================================
Protects against Railway's ephemeral filesystem wiping all server configs.

How it works:
  • Every 1 minute: compress all DB tables → send as .gz file to BACKUP_CHANNEL_ID
  • On startup: Intelligence-First Restoration scans for the largest/latest backup
  • Users never notice. Configs survive any number of redeploys.
"""

import discord
import aiosqlite
import asyncio
import logging
import json
import gzip
import io
import os
from datetime import datetime

logger = logging.getLogger("XERO.Backup")

BACKUP_CHANNEL_ID = int(os.getenv("BACKUP_CHANNEL_ID", "0"))
DB_PATH           = os.getenv("DB_PATH", "data/xero.db")

BACKUP_TABLES = [
    "guild_settings",
    "levels",
    "economy",
    "economy_streaks",
    "warnings",
    "mod_cases",
    "birthdays",
    "level_rewards",
    "reaction_role_panels",
    "starboard_config",
    "starboard_messages",
    "verification_config",
    "tickets",
    "temp_voice_config",
    "autoresponder_rules",
    "custom_commands",
    "reputation",
    "marriages",
    "stocks",
    "stock_portfolio",
    "user_stats",
    "afk_users",
    "suggestions",
    "member_roles",
    "economy_transactions",
    "personality_log",
    "counting_config",
    "log_ignored_channels",
    "log_ignored_roles",
    "user_verifications"
]


async def export_db(bot: discord.Client) -> bytes:
    """Export all critical tables as gzip-compressed JSON. Typically 50–500KB."""
    data: dict[str, list] = {}
    for table in BACKUP_TABLES:
        try:
            async with bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(f"SELECT * FROM {table}") as c:
                    rows = await c.fetchall()
                    data[table] = [dict(r) for r in rows]
        except Exception:
            pass
    payload = {
        "timestamp": datetime.utcnow().isoformat(),
        "tables":    data,
        "version":   "xero_v4_aegis",
        "row_counts": {t: len(v) for t, v in data.items()},
    }
    json_bytes = json.dumps(payload, default=str).encode("utf-8")
    buf = io.BytesIO()
    with gzip.GzipFile(fileobj=buf, mode="wb", compresslevel=9) as gz:
        gz.write(json_bytes)
    return buf.getvalue()


async def import_db(bot: discord.Client, backup_bytes: bytes) -> int:
    """Restore all tables from a gzip-compressed JSON backup. Returns row count."""
    buf = io.BytesIO(backup_bytes)
    with gzip.GzipFile(fileobj=buf, mode="rb") as gz:
        payload = json.loads(gz.read().decode("utf-8"))
    tables    = payload.get("tables", {})
    total_rows = 0
    async with bot.db._db_context() as db:
        # Clear tables first to ensure clean state
        for table in tables.keys():
            try: await db.execute(f"DELETE FROM {table}")
            except: pass
            
        for table, rows in tables.items():
            if not rows:
                continue
            for row in rows:
                cols         = list(row.keys())
                placeholders = ", ".join("?" for _ in cols)
                col_str      = ", ".join(cols)
                values       = [row[c] for c in cols]
                try:
                    await db.execute(
                        f"INSERT OR REPLACE INTO {table} ({col_str}) VALUES ({placeholders})",
                        values,
                    )
                    total_rows += 1
                except Exception:
                    pass
        await db.commit()
    logger.info(f"✓ DB restored: {len(tables)} tables, {total_rows} rows")
    return total_rows


async def is_db_empty(bot: discord.Client) -> bool:
    """True if critical tables have no rows."""
    try:
        async with bot.db._db_context() as db:
            async with db.execute("SELECT COUNT(*) FROM guild_settings") as c:
                row = await c.fetchone()
                return row[0] == 0
    except Exception:
        return True


async def auto_restore(bot: discord.Client) -> bool:
    """
    Intelligence-First Restoration:
    Scans the backup channel for the largest and most recent valid backup.
    """
    if not BACKUP_CHANNEL_ID:
        logger.info("BACKUP_CHANNEL_ID not set — skipping auto-restore.")
        return False

    logger.info("🔍 Starting Intelligence-First Database Restoration...")
    
    try:
        channel = bot.get_channel(BACKUP_CHANNEL_ID)
        if not channel:
            channel = await bot.fetch_channel(BACKUP_CHANNEL_ID)
    except Exception as e:
        logger.error(f"Cannot access backup channel {BACKUP_CHANNEL_ID}: {e}")
        return False

    candidates = []
    async for msg in channel.history(limit=200):
        if not msg.attachments: continue
        for att in msg.attachments:
            if att.filename.startswith("xero_backup_") and att.filename.endswith(".gz"):
                # We store (size, timestamp, attachment_url, filename)
                candidates.append({
                    "size": att.size,
                    "time": msg.created_at,
                    "url":  att.url,
                    "name": att.filename
                })

    if not candidates:
        logger.warning("No valid backups found in channel. Starting fresh.")
        return False

    # Intelligence logic: Sort by size (desc) and then time (desc)
    # This ensures we pick the MOST COMPLETE data even if a newer small/empty backup exists.
    candidates.sort(key=lambda x: (x["size"], x["time"]), reverse=True)
    
    best = candidates[0]
    logger.info(f"💎 Best backup candidate: {best['name']} ({best['size']//1024}KB) from {best['time']}")
    
    # Safety: If the best backup is under 10KB, it's likely empty or corrupted.
    if best["size"] < 10240:
        logger.warning(f"Best candidate is suspiciously small ({best['size']//1024}KB < 10KB). Aborting restore to prevent data wipe.")
        return False

    try:
        import aiohttp
        async with aiohttp.ClientSession() as s:
            async with s.get(best["url"], timeout=aiohttp.ClientTimeout(total=60)) as r:
                backup_bytes = await r.read()
        
        rows = await import_db(bot, backup_bytes)
        logger.info(f"✅ Intelligence-First Restore Success: {rows} rows recovered.")
        return True
    except Exception as e:
        logger.error(f"Restore failed: {e}")
        return False


async def send_backup(bot: discord.Client, triggered_by: str = "auto") -> bool:
    """Send a compressed DB backup to the backup channel."""
    if not BACKUP_CHANNEL_ID:
        return False
        
    try:
        # Safety: Never back up an empty database automatically
        if triggered_by in ("auto-1min", "startup_sync"):
            if await is_db_empty(bot):
                logger.warning(f"⚠ Skipping {triggered_by} backup: Database contains no server settings.")
                return False

        backup_bytes = await export_db(bot)
        timestamp    = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        fname        = f"xero_backup_{timestamp}.gz"
        
        channel = bot.get_channel(BACKUP_CHANNEL_ID) or await bot.fetch_channel(BACKUP_CHANNEL_ID)
        
        # Meta analysis for the log message
        buf = io.BytesIO(backup_bytes)
        with gzip.GzipFile(fileobj=buf, mode="rb") as gz:
            meta = json.loads(gz.read())
        
        guilds = len(meta["tables"].get("guild_settings", []))
        total  = sum(len(v) for v in meta["tables"].values())
        
        files = [discord.File(io.BytesIO(backup_bytes), filename=fname)]
        
        # If this is a guild-specific trigger, try to include the banner for visual confirmation
        image_info = ""
        if triggered_by == "guild_join" or triggered_by == "manual":
            settings = await bot.db.get_guild_settings(bot.guilds[0].id) # Just an example, ideally we'd pass guild_id
            url = settings.get("unified_image_url")
            if url:
                image_info = f"\n🖼️ **Unified Banner:** [View Image]({url})"

        await channel.send(
            content=(
                f"📦 **XERO Elite Backup** | `{timestamp} UTC` | trigger: `{triggered_by}`\n"
                f"**{guilds}** servers • **{total}** rows • `{len(backup_bytes)//1024}KB`{image_info}"
            ),
            files=files,
        )
        logger.info(f"✅ Backup: {fname} | {guilds} guilds | {total} rows | {len(backup_bytes)//1024}KB")
        return True
    except Exception as e:
        logger.error(f"Backup failed: {e}")
        return False
