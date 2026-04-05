"""
XERO Bot — Main Entry Point
Advanced AI-Powered Discord Bot by Team Flame
300+ Commands | NVIDIA Llama | All Premium Features Free
"""
import discord
from discord.ext import commands
from discord.ext import tasks
import os, logging, asyncio, time
from database import Database
from utils.nvidia_api import NvidiaAPI
from utils.db_backup import auto_restore, send_backup, BACKUP_CHANNEL_ID
from dotenv import load_dotenv

load_dotenv()
os.makedirs("logs", exist_ok=True)
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(name)s] %(levelname)s: %(message)s",
    handlers=[logging.FileHandler("logs/xero.log"), logging.StreamHandler()]
)
logger = logging.getLogger("XERO")

class XeroBot(commands.Bot):
    def __init__(self):
        intents = discord.Intents.all()
        super().__init__(
            command_prefix=commands.when_mentioned_or("/"),
            intents=intents,
            help_command=None,
            case_insensitive=True,
        )
        self.db          = Database()
        self.nvidia      = NvidiaAPI(
            primary_key = os.getenv("NVIDIA_MAIN_KEY",   os.getenv("NVIDIA_API_KEY", "")),
            vision_key  = os.getenv("NVIDIA_VISION_KEY", os.getenv("NVIDIA_API_KEY", "")),
        )
        self.launch_time = time.time()
        self.MANAGEMENT_GUILD_ID = int(os.getenv("MANAGEMENT_GUILD_ID", "1431852658767040535"))
        self._synced = False  # prevent double-sync on reconnect
        self.initial_extensions = [
            "cogs.events", "cogs.config", "cogs.setup", "cogs.info", "cogs.admin",
            "cogs.moderation", "cogs.automod", "cogs.smart_mod",
            "cogs.economy", "cogs.economy_advanced",
            "cogs.levels", "cogs.leaderboard",
            "cogs.ai", "cogs.ai_advanced",
            "cogs.fun", "cogs.social", "cogs.engagement", "cogs.personality",
            "cogs.birthday", "cogs.suggestions", "cogs.reactionroles", "cogs.starboard",
            "cogs.custom_commands", "cogs.giveaway", "cogs.announcement",
            "cogs.verification", "cogs.tickets", "cogs.roles", "cogs.server",
            "cogs.temp_voice",
            "cogs.security",
            "cogs.server_features",
            "cogs.profile_extras",
            "cogs.voice_ai",
            "cogs.member_intelligence",
            "cogs.autoresponder",
            "cogs.logging_system",
            "cogs.branding",
            "cogs.tools", "cogs.profile", "cogs.analytics",
            "cogs.utility", "cogs.backup", "cogs.core_admin", "cogs.help",
        ]

    async def setup_hook(self):
        os.makedirs("data", exist_ok=True)
        await self.db.initialize()
        if hasattr(self.db, 'initialize_advanced'):
            await self.db.initialize_advanced()
        if hasattr(self.db, 'initialize_xero_tables'):
            await self.db.initialize_xero_tables()
        if hasattr(self.db, 'initialize_v4_tables'):
            await self.db.initialize_v4_tables()
        logger.info("✓ Database fully initialized.")

        failed_cogs = []
        for ext in self.initial_extensions:
            try:
                await self.load_extension(ext)
                logger.info(f"  ✓ {ext}")
            except Exception as e:
                logger.error(f"  ✗ {ext} — {e}")
                failed_cogs.append((ext, str(e)))

        if failed_cogs:
            logger.warning(f"  {len(failed_cogs)} cog(s) failed to load:")
            for cog, err in failed_cogs:
                logger.warning(f"    - {cog}: {err}")

        logger.info(f"✓ Management Guild ID: {self.MANAGEMENT_GUILD_ID}")

    async def on_ready(self):
        logger.info(
            f"✓ XERO ready — {self.user} | {len(self.guilds)} guilds | "
            f"{sum(g.member_count for g in self.guilds):,} users | "
            f"{round(self.latency * 1000)}ms"
        )
        await self.change_presence(
            activity=discord.Activity(type=discord.ActivityType.watching, name="300+ commands | /help")
        )

        # Only run startup tasks once per process start
        if self._synced:
            return
        self._synced = True

        # ── Intelligence-First Auto-Restore (Railway Ephemeral Protection) ──
        if BACKUP_CHANNEL_ID:
            restored = await auto_restore(self)
            if restored:
                logger.info("✓ XERO Intelligence-First: Server configs and levels restored from elite backup.")
            else:
                from utils.db_backup import is_db_empty
                if not await is_db_empty(self):
                    from utils.db_backup import send_backup
                    await send_backup(self, triggered_by="startup_sync")
                    logger.info("✓ DB persistence check passed — current state is stable.")
                else:
                    logger.warning("⚠ DB is empty and no valid backup found. Starting fresh to avoid overwriting.")
        else:
            logger.info("ℹ️  BACKUP_CHANNEL_ID not set.")

        # ── Start the 1-min auto-backup loop ──────────────────────────────────
        if not self._backup_loop.is_running():
            self._backup_loop.start()

        # ── Deep-Level Command Reconstruction ──────────────────────────────────────────────────
        # We perform a clean global sync.
        try:
            # 1. Sync global tree
            # FORCE SYNC on every startup with retry logic for rate limits.
            try:
                logger.info("🔄 Forcing deep-level global command sync...")
                synced = await self.tree.sync()
                logger.info(f"✅ SUCCESS: Synced {len(synced)} global slash commands.")
            except discord.HTTPException as e:
                if e.code == 429:
                    logger.warning("⚠️ Rate limited during sync — retrying in 30s...")
                    await asyncio.sleep(30)
                    synced = await self.tree.sync()
                    logger.info(f"✅ SUCCESS: Synced {len(synced)} global slash commands after retry.")
                else:
                    raise e
            
            # 3. Explicitly sync to management guild to ensure /core is visible
            # We use a small delay to ensure global sync is processed first
            await asyncio.sleep(5)
            mguild = discord.Object(id=self.MANAGEMENT_GUILD_ID)
            self.tree.copy_global_to(guild=mguild)
            await self.tree.sync(guild=mguild)
            logger.info(f"✅ Management Guild ({self.MANAGEMENT_GUILD_ID}) force-synced.")
        except Exception as e:
            logger.error(f"❌ Deep-Level Sync failed: {e}")

    @tasks.loop(minutes=1)
    async def _backup_loop(self):
        """Automatically backs up the DB every 1 minute to the backup channel."""
        try:
            await send_backup(self, triggered_by="auto-1min")
        except Exception as e:
            logger.error(f"Backup loop error: {e}")

    @_backup_loop.before_loop
    async def _before_backup_loop(self):
        await self.wait_until_ready()

    async def on_guild_join(self, guild: discord.Guild):
        """Trigger an immediate backup when joining a new server."""
        logger.info(f"✓ Joined new guild: {guild.name} ({guild.id}) — triggering instant backup.")
        await send_backup(self, triggered_by="guild_join")


    async def on_interaction(self, interaction: discord.Interaction):
        """Dispatch every interaction — slash commands via the app_commands tree,
        buttons/selects/modals are handled automatically by the view store."""
        await self.tree.call(interaction)

    async def on_app_command_error(self, interaction: discord.Interaction, error: discord.app_commands.AppCommandError):
        from utils.embeds import error_embed
        original = getattr(error, "original", error)
        if isinstance(error, discord.app_commands.MissingPermissions):
            msg = f"You need: `{'`, `'.join(error.missing_permissions)}`"
        elif isinstance(error, discord.app_commands.BotMissingPermissions):
            msg = f"I need: `{'`, `'.join(error.missing_permissions)}`"
        elif isinstance(error, discord.app_commands.CommandOnCooldown):
            msg = f"Slow down! Try again in **{error.retry_after:.1f}s**"
        elif isinstance(error, discord.app_commands.CheckFailure):
            msg = "You don't have permission to use this command."
        elif isinstance(original, asyncio.TimeoutError):
            msg = "Request timed out. Please try again."
        else:
            msg = "Something went wrong. Please try again."
            logger.error(
                f"Command error in {getattr(interaction.command, 'name', 'unknown')}: {original}",
                exc_info=original,
            )
        try:
            embed = error_embed("Error", msg)
            if interaction.response.is_done():
                await interaction.followup.send(embed=embed, ephemeral=True)
            else:
                await interaction.response.send_message(embed=embed, ephemeral=True)
        except Exception:
            pass


bot_instance = None

async def main():
    global bot_instance
    bot = XeroBot()
    bot_instance = bot
    token = os.getenv("DISCORD_TOKEN")
    if not token:
        logger.critical("DISCORD_TOKEN not set — cannot start."); return
    async with bot:
        await bot.start(token)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("XERO Bot shut down.")
