"""
XERO Bot — Smart Moderation (8 commands)
Raid detection, auto-escalation, mass-join protection, server health AI analysis.
This is what makes staff teams actually rely on XERO over every other bot.
"""
import discord
from utils.guard import command_guard
from discord.ext import commands, tasks
from discord import app_commands
import logging
import datetime
import aiosqlite
from utils.embeds import (
    success_embed, error_embed, info_embed, comprehensive_embed,
    raid_alert_embed, escalation_embed, health_embed, XERO, FOOTER_MOD
)

logger = logging.getLogger("XERO.SmartMod")

# Recent join tracking: guild_id -> list of join timestamps
JOIN_TRACKER: dict = {}


class SmartMod(commands.GroupCog, name="smart"):
    def __init__(self, bot):
        self.bot = bot
        self.cleanup_join_tracker.start()

    def cog_unload(self):
        self.cleanup_join_tracker.cancel()

    @tasks.loop(minutes=2)
    async def cleanup_join_tracker(self):
        """Remove stale join timestamps older than 5 minutes."""
        cutoff = datetime.datetime.now() - datetime.timedelta(minutes=5)
        for guild_id in list(JOIN_TRACKER.keys()):
            JOIN_TRACKER[guild_id] = [t for t in JOIN_TRACKER[guild_id] if t > cutoff]

    @cleanup_join_tracker.before_loop
    async def before_cleanup(self):
        await self.bot.wait_until_ready()

    async def handle_member_join_check(self, member: discord.Member):
        """Called from events.py on_member_join — checks for raid."""
        settings = await self.bot.db.get_guild_settings(member.guild.id)
        if not settings.get("raid_protection", 1):
            return

        gid       = member.guild.id
        threshold = settings.get("raid_threshold", 5)
        window    = settings.get("raid_window", 30)  # seconds

        if gid not in JOIN_TRACKER:
            JOIN_TRACKER[gid] = []
        JOIN_TRACKER[gid].append(datetime.datetime.now())

        # Count joins within window
        cutoff     = datetime.datetime.now() - datetime.timedelta(seconds=window)
        recent     = [t for t in JOIN_TRACKER[gid] if t > cutoff]
        join_count = len(recent)

        if join_count >= threshold:
            await self._trigger_raid_protection(member.guild, join_count, window, settings)

    async def _trigger_raid_protection(self, guild: discord.Guild, count: int, window: int, settings: dict):
        """Lock server + alert admins when raid detected."""
        # Clear tracker to avoid repeat triggers
        JOIN_TRACKER[guild.id] = []

        # Lock all text channels
        locked = 0
        for ch in guild.text_channels:
            try:
                ow = ch.overwrites_for(guild.default_role)
                ow.send_messages = False
                await ch.set_permissions(guild.default_role, overwrite=ow)
                locked += 1
            except Exception:
                pass

        # Log
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT INTO raid_log (guild_id, join_count, action_taken) VALUES (?,?,?)",
                (guild.id, count, f"auto_lockdown_{locked}_channels")
            )
            await db.commit()

        embed = raid_alert_embed(guild, count, window)

        # Send to log channel
        log_ch_id = settings.get("log_channel_id")
        if log_ch_id:
            ch = guild.get_channel(log_ch_id)
            if ch:
                try:
                    await ch.send(embed=embed)
                except Exception:
                    pass

        # DM all admins
        for member in guild.members:
            if member.guild_permissions.administrator and not member.bot:
                try:
                    await member.send(embed=embed)
                except Exception:
                    pass

        logger.warning(f"🚨 Raid detected in {guild.name} — {count} joins in {window}s. Locked {locked} channels.")

    async def check_auto_escalation(self, guild: discord.Guild, user: discord.Member, warn_count: int, reason: str):
        """Called after every warn — auto-escalates at thresholds."""
        settings = await self.bot.db.get_guild_settings(guild.id)
        if not settings.get("auto_escalate", 1):
            return None

        action_taken = None

        # Thresholds: 3 warns = timeout, 5 warns = ban
        if warn_count == 3:
            try:
                until = discord.utils.utcnow() + datetime.timedelta(hours=1)
                await user.timeout(until, reason=f"XERO Auto-Escalation: 3 warnings")
                action_taken = "1 hour timeout"
            except Exception as e:
                logger.error(f"Auto-escalation timeout error: {e}")
                action_taken = "timeout failed (check permissions)"

        elif warn_count == 5:
            try:
                await user.ban(reason="XERO Auto-Escalation: 5 warnings", delete_message_days=0)
                action_taken = "banned"
            except Exception as e:
                logger.error(f"Auto-escalation ban error: {e}")
                action_taken = "ban failed (check permissions)"

        if action_taken:
            embed = escalation_embed(user, warn_count, action_taken, reason)
            log_ch_id = settings.get("log_channel_id")
            if log_ch_id:
                ch = guild.get_channel(log_ch_id)
                if ch:
                    try:
                        await ch.send(embed=embed)
                    except Exception:
                        pass

        return action_taken

    # ── /smart health ──────────────────────────────────────────────────────
    @app_commands.command(name="health", description="Get an AI-powered server health score — mod activity, member retention, bot usage.")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def health(self, interaction: discord.Interaction):
        await interaction.response.defer()

        guild = interaction.guild

        # Gather stats for AI
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT COUNT(*) FROM mod_cases WHERE guild_id=?", (guild.id,)) as c:
                total_cases = (await c.fetchone())[0]
            async with db.execute("SELECT COUNT(*) FROM warnings WHERE guild_id=?", (guild.id,)) as c:
                total_warns = (await c.fetchone())[0]
            async with db.execute("SELECT COUNT(*) FROM mod_cases WHERE guild_id=? AND timestamp > datetime('now', '-7 days')", (guild.id,)) as c:
                recent_cases = (await c.fetchone())[0]
            async with db.execute("SELECT SUM(commands_used), SUM(messages_sent) FROM user_stats WHERE guild_id=?", (guild.id,)) as c:
                activity = await c.fetchone()
            async with db.execute("SELECT COUNT(*) FROM raid_log WHERE guild_id=? AND timestamp > datetime('now', '-30 days')", (guild.id,)) as c:
                raid_attempts = (await c.fetchone())[0]
            async with db.execute("SELECT COUNT(DISTINCT user_id) FROM user_stats WHERE guild_id=? AND commands_used > 5", (guild.id,)) as c:
                active_users = (await c.fetchone())[0]

        total_cmds = activity[0] or 0
        total_msgs = activity[1] or 0

        # Build score (0-100)
        score = 70  # base

        # Member activity bonus
        activity_ratio = active_users / max(guild.member_count, 1)
        if activity_ratio > 0.3:   score += 15
        elif activity_ratio > 0.1: score += 8
        elif activity_ratio < 0.02: score -= 15

        # Mod activity — some cases is healthy, too many or too few isn't
        if 0 < recent_cases <= 10:   score += 5
        elif recent_cases == 0:      score -= 5  # possibly unmoderated
        elif recent_cases > 30:      score -= 10

        # Raid attempts
        if raid_attempts > 3:       score -= 20
        elif raid_attempts > 0:     score -= 5

        # Setup quality
        settings = await self.bot.db.get_guild_settings(guild.id)
        setup_items = ["welcome_channel_id", "log_channel_id", "verify_role_id"]
        configured  = sum(1 for k in setup_items if settings.get(k))
        score += configured * 3

        # Bot features enabled
        if settings.get("leveling_enabled", 1):  score += 2
        if settings.get("economy_enabled", 1):   score += 2
        if settings.get("automod_enabled", 0):   score += 3
        if settings.get("ai_enabled", 1):        score += 2

        score = max(0, min(100, score))
        grade = "A" if score >= 90 else "B" if score >= 75 else "C" if score >= 60 else "D" if score >= 45 else "F"

        # AI analysis
        prompt = (
            f"Analyze this Discord server's health data and give a concise 2-3 sentence assessment:\n\n"
            f"Server: {guild.name} ({guild.member_count} members)\n"
            f"Active users (5+ commands): {active_users} ({activity_ratio*100:.1f}%)\n"
            f"Total commands used: {total_cmds:,}\n"
            f"Total messages: {total_msgs:,}\n"
            f"Mod cases (all time): {total_cases} | Last 7 days: {recent_cases}\n"
            f"Warnings: {total_warns}\n"
            f"Raid attempts (30 days): {raid_attempts}\n"
            f"Setup: {'good' if configured >= 2 else 'incomplete'}\n"
            f"Health Score: {score}/100\n\n"
            f"Be specific, practical, and honest. Focus on the most important insight."
        )
        analysis = await self.bot.nvidia.ask(prompt) or "Unable to generate analysis."

        # Recommendations
        recs = []
        if not settings.get("log_channel_id"):  recs.append("Set a mod log channel with `/config set-logs`")
        if not settings.get("verify_role_id"):  recs.append("Add verification with `/verify setup`")
        if not settings.get("automod_enabled"): recs.append("Enable AutoMod with `/automod setup`")
        if activity_ratio < 0.1:               recs.append("Run a giveaway to boost engagement")
        if raid_attempts > 0:                  recs.append("Review raid protection settings with `/smart raid-config`")
        if recent_cases > 20:                  recs.append("High mod volume — consider if AutoMod can handle some cases")

        # Cache
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO health_cache (guild_id, score, analysis) VALUES (?,?,?)",
                (guild.id, score, analysis)
            )
            await db.commit()

        embed = health_embed(guild, score, grade, analysis, recs)
        embed.add_field(name="📊  Raw Data", value=(
            f"Active Users: **{active_users}** / {guild.member_count}\n"
            f"Commands: **{total_cmds:,}**  |  Messages: **{total_msgs:,}**\n"
            f"Mod Cases (7d): **{recent_cases}**  |  Raids (30d): **{raid_attempts}**"
        ), inline=False)
        await interaction.followup.send(embed=embed)

    # ── /smart raid-config ─────────────────────────────────────────────────
    @app_commands.command(name="raid-config", description="Configure raid detection settings — threshold, window, and on/off.")
    @app_commands.describe(enabled="Enable or disable raid protection", threshold="Joins to trigger protection (default 5)", window_seconds="Time window in seconds (default 30)")
    @app_commands.checks.has_permissions(administrator=True)
    async def raid_config(self, interaction: discord.Interaction, enabled: bool = True, threshold: int = 5, window_seconds: int = 30):
        threshold      = max(3, min(50, threshold))
        window_seconds = max(10, min(300, window_seconds))
        await self.bot.db.update_guild_setting(interaction.guild.id, "raid_protection", 1 if enabled else 0)
        await self.bot.db.update_guild_setting(interaction.guild.id, "raid_threshold", threshold)
        await self.bot.db.update_guild_setting(interaction.guild.id, "raid_window", window_seconds)
        embed = success_embed(
            "Raid Protection Configured",
            f"**Status:** {'✅ Enabled' if enabled else '❌ Disabled'}\n"
            f"**Trigger:** {threshold} joins within **{window_seconds}s**\n"
            f"**Action:** Auto-lock all channels + DM all admins\n\n"
            f"*XERO will automatically defend your server when a raid is detected.*"
        )
        embed.set_footer(text="XERO Smart Moderation")
        await interaction.response.send_message(embed=embed)

    # ── /smart escalation-config ───────────────────────────────────────────
    @app_commands.command(name="escalation-config", description="Configure auto-escalation — what happens at 3 and 5 warnings.")
    @app_commands.describe(enabled="Enable or disable auto-escalation")
    @app_commands.checks.has_permissions(administrator=True)
    async def escalation_config(self, interaction: discord.Interaction, enabled: bool = True):
        await self.bot.db.update_guild_setting(interaction.guild.id, "auto_escalate", 1 if enabled else 0)
        embed = success_embed(
            "Auto-Escalation Configured",
            f"**Status:** {'✅ Enabled' if enabled else '❌ Disabled'}\n\n"
            f"**Escalation Ladder:**\n"
            f"⚠️ **3 warnings** → Auto 1-hour timeout\n"
            f"🔨 **5 warnings** → Auto permanent ban\n\n"
            f"*All auto-actions are logged to your mod log channel.*"
        )
        embed.set_footer(text="XERO Smart Moderation")
        await interaction.response.send_message(embed=embed)

    # ── /smart raid-log ────────────────────────────────────────────────────
    @app_commands.command(name="raid-log", description="View the history of raid attempts and auto-lockdowns in this server.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def raid_log(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM raid_log WHERE guild_id=? ORDER BY timestamp DESC LIMIT 10",
                (interaction.guild.id,)
            ) as c:
                logs = [dict(r) for r in await c.fetchall()]

        if not logs:
            return await interaction.response.send_message(embed=success_embed(
                "No Raids Detected",
                "No raid attempts have been logged for this server. Your server is safe! 🛡️"
            ))

        embed = comprehensive_embed(
            title="🚨  Raid Detection History",
            description=f"**{len(logs)}** raid attempt(s) logged",
            color=XERO.DANGER
        )
        for log in logs:
            ts = int(datetime.datetime.fromisoformat(log["timestamp"]).timestamp())
            embed.add_field(
                name=f"<t:{ts}:R>",
                value=f"**Joins detected:** {log['join_count']}\n**Action:** {log['action_taken']}",
                inline=True
            )
        embed.set_footer(text="XERO Smart Moderation  •  Auto-Raid Protection")
        await interaction.response.send_message(embed=embed)

    # ── /smart lockdown ────────────────────────────────────────────────────
    @app_commands.command(name="lockdown", description="Emergency manual server lockdown — locks all channels instantly.")
    @app_commands.describe(reason="Reason for lockdown (shown to members)")
    @app_commands.checks.has_permissions(administrator=True)
    async def lockdown(self, interaction: discord.Interaction, reason: str = "Emergency lockdown"):
        await interaction.response.defer()
        count = 0
        for ch in interaction.guild.text_channels:
            ow = ch.overwrites_for(interaction.guild.default_role)
            ow.send_messages = False
            try:
                await ch.set_permissions(interaction.guild.default_role, overwrite=ow)
                count += 1
            except Exception:
                pass
        embed = discord.Embed(
            title="🔴  SERVER LOCKDOWN ACTIVE",
            description=f"**{count}** channels locked by {interaction.user.mention}\n**Reason:** {reason}\n\nUse `/smart unlockdown` to restore access.",
            color=XERO.DANGER,
            timestamp=discord.utils.utcnow(),
        )
        embed.set_footer(text="XERO Smart Moderation")
        await interaction.followup.send(embed=embed)
        logger.warning(f"Manual lockdown in {interaction.guild.name} by {interaction.user}")

    # ── /smart unlockdown ──────────────────────────────────────────────────
    @app_commands.command(name="unlockdown", description="Lift the server lockdown — restores all channel access.")
    @app_commands.checks.has_permissions(administrator=True)
    async def unlockdown(self, interaction: discord.Interaction):
        await interaction.response.defer()
        count = 0
        for ch in interaction.guild.text_channels:
            ow = ch.overwrites_for(interaction.guild.default_role)
            ow.send_messages = None
            try:
                await ch.set_permissions(interaction.guild.default_role, overwrite=ow)
                count += 1
            except Exception:
                pass
        embed = success_embed(
            "🟢  Lockdown Lifted",
            f"**{count}** channels unlocked by {interaction.user.mention}\nThe server is back to normal."
        )
        embed.set_footer(text="XERO Smart Moderation")
        await interaction.followup.send(embed=embed)

    # ── /smart warn-stats ──────────────────────────────────────────────────
    @app_commands.command(name="warn-stats", description="View warning statistics — top offenders, trends, most common reasons.")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def warn_stats(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("""
                SELECT user_id, COUNT(*) as count FROM warnings
                WHERE guild_id=? GROUP BY user_id ORDER BY count DESC LIMIT 5
            """, (interaction.guild.id,)) as c:
                top_offenders = [dict(r) for r in await c.fetchall()]

            async with db.execute("""
                SELECT COUNT(*) as total,
                       SUM(CASE WHEN timestamp > datetime('now', '-7 days') THEN 1 ELSE 0 END) as week,
                       SUM(CASE WHEN timestamp > datetime('now', '-30 days') THEN 1 ELSE 0 END) as month
                FROM warnings WHERE guild_id=?
            """, (interaction.guild.id,)) as c:
                totals = await c.fetchone()

        embed = comprehensive_embed(
            title="📊  Warning Statistics",
            description=f"**Total:** {totals['total']}  •  **This Week:** {totals['week']}  •  **This Month:** {totals['month']}",
            color=XERO.WARNING
        )
        if top_offenders:
            embed.add_field(name="⚠️  Top Offenders", value="\n".join(
                f"**{i+1}.** <@{r['user_id']}> — {r['count']} warning(s)"
                for i, r in enumerate(top_offenders)
            ), inline=False)

        # Trend
        trend = "📈 Increasing" if totals["week"] > (totals["month"] - totals["week"]) / 3 else "📉 Decreasing"
        embed.add_field(name="📉  Trend", value=trend, inline=True)
        embed.set_footer(text="XERO Smart Moderation")
        await interaction.followup.send(embed=embed)


async def setup(bot):
    await bot.add_cog(SmartMod(bot))
