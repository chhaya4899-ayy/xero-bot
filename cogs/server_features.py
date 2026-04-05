"""
XERO Bot — Server Features
Auto-updating stats channels, bump reminder, message logger, weekly reward, double XP.
All free. All better than MEE6/Carl-bot premium.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, datetime, asyncio, aiosqlite, random
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed, XERO, FOOTER_MAIN, FOOTER_ECO

logger = logging.getLogger("XERO.ServerFeatures")

# Active double XP events: guild_id -> expires_at datetime
DOUBLE_XP_EVENTS: dict = {}


class ServerFeatures(commands.GroupCog, name="features"):
    def __init__(self, bot):
        self.bot = bot
        self.update_stats_channels.start()
        self.check_bump_reminders.start()

    def cog_unload(self):
        self.update_stats_channels.cancel()
        self.check_bump_reminders.cancel()

    def is_double_xp(self, guild_id: int) -> bool:
        expires = DOUBLE_XP_EVENTS.get(guild_id)
        if expires and datetime.datetime.now() < expires:
            return True
        DOUBLE_XP_EVENTS.pop(guild_id, None)
        return False

    # ── Background: Update stats channels every 10 minutes ────────────────
    @commands.Cog.listener()
    async def on_ready(self):
        if not self.update_stats_channels.is_running():
            self.update_stats_channels.start()

    @discord.ext.tasks.loop(minutes=10)
    async def update_stats_channels(self):
        import aiosqlite
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute("SELECT * FROM stats_channels") as c:
                    all_configs = await c.fetchall()
            for row in all_configs:
                guild_id, channel_id, stat_type = row[0], row[1], row[2]
                guild = self.bot.get_guild(guild_id)
                if not guild: continue
                ch = guild.get_channel(channel_id)
                if not ch or not isinstance(ch, discord.VoiceChannel): continue
                try:
                    name = self._stats_channel_name(guild, stat_type)
                    if ch.name != name:
                        await ch.edit(name=name, reason="XERO Stats Channel Update")
                except Exception as e:
                    logger.debug(f"Stats channel update: {e}")
        except Exception as e:
            logger.error(f"Stats channel loop: {e}")

    @update_stats_channels.before_loop
    async def before_stats(self): await self.bot.wait_until_ready()

    def _stats_channel_name(self, guild: discord.Guild, stat_type: str) -> str:
        online = sum(1 for m in guild.members if m.status != discord.Status.offline and not m.bot)
        bots   = sum(1 for m in guild.members if m.bot)
        humans = guild.member_count - bots
        names  = {
            "members":  f"👥 Members: {guild.member_count:,}",
            "humans":   f"🧑 Humans: {humans:,}",
            "bots":     f"🤖 Bots: {bots:,}",
            "online":   f"🟢 Online: {online:,}",
            "boosts":   f"💎 Boosts: {guild.premium_subscription_count}",
            "channels": f"📡 Channels: {len(guild.channels)}",
            "roles":    f"🎭 Roles: {len(guild.roles)}",
        }
        return names.get(stat_type, f"📊 {stat_type}: {guild.member_count:,}")

    # ── Background: Bump reminders ─────────────────────────────────────────
    @discord.ext.tasks.loop(minutes=5)
    async def check_bump_reminders(self):
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT guild_id, channel_id, next_bump FROM bump_reminders WHERE next_bump <= datetime('now') AND enabled=1"
                ) as c:
                    due = await c.fetchall()
            for guild_id, channel_id, _ in due:
                guild = self.bot.get_guild(guild_id)
                if not guild: continue
                ch = guild.get_channel(channel_id)
                if not ch: continue
                from utils.embeds import XERO, comprehensive_embed
                embed = discord.Embed(
                    title="⬆️  Time to Bump!",
                    description=(
                        "It's been **2 hours** — time to bump your server!\n\n"
                        "**Disboard:** Type `/bump` in this channel\n"
                        "**Top.gg:** Use `/vote` to get rewards + visibility\n\n"
                        "*Regular bumping keeps you visible on listing sites and attracts new members.*"
                    ),
                    color=XERO.GOLD
                )
                embed.set_footer(text="XERO Bump Reminder  •  Growing your community")
                try:
                    settings = await self.bot.db.get_guild_settings(guild_id)
                    role_id  = settings.get("bump_role_id")
                    content  = f"<@&{role_id}>" if role_id else None
                    await ch.send(content=content, embed=embed)
                    # Schedule next bump in 2 hours
                    next_bump = (datetime.datetime.utcnow() + datetime.timedelta(hours=2)).strftime("%Y-%m-%d %H:%M:%S")
                    async with self.bot.db._db_context() as db:
                        await db.execute("UPDATE bump_reminders SET next_bump=? WHERE guild_id=?", (next_bump, guild_id))
                        await db.commit()
                except Exception as e:
                    logger.error(f"Bump reminder send: {e}")
        except Exception as e:
            logger.debug(f"Bump reminder loop: {e}")

    @check_bump_reminders.before_loop
    async def before_bumps(self): await self.bot.wait_until_ready()

    # ── /features stats-channel ────────────────────────────────────────────
    @app_commands.command(name="stats-channel", description="Create an auto-updating voice channel that shows live server stats. MEE6 charges $9/mo for this.")
    @app_commands.describe(stat="What stat to display", channel="Existing voice channel to use (or leave blank to create new)")
    @app_commands.choices(stat=[
        app_commands.Choice(name="👥 Total Members",  value="members"),
        app_commands.Choice(name="🧑 Human Members",  value="humans"),
        app_commands.Choice(name="🤖 Bot Count",       value="bots"),
        app_commands.Choice(name="🟢 Online Members", value="online"),
        app_commands.Choice(name="💎 Boost Count",    value="boosts"),
        app_commands.Choice(name="📡 Channel Count",  value="channels"),
        app_commands.Choice(name="🎭 Role Count",     value="roles"),
    ])
    @app_commands.checks.has_permissions(manage_channels=True)
    async def stats_channel(self, interaction: discord.Interaction, stat: str, channel: discord.VoiceChannel = None):
        await interaction.response.defer()
        import aiosqlite
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS stats_channels (
                    guild_id INTEGER, channel_id INTEGER, stat_type TEXT,
                    PRIMARY KEY(guild_id, stat_type)
                )
            """)
            await db.commit()

        # Create or use existing channel
        if not channel:
            category = interaction.channel.category
            name     = self._stats_channel_name(interaction.guild, stat)
            try:
                channel = await interaction.guild.create_voice_channel(
                    name=name, category=category,
                    overwrites={interaction.guild.default_role: discord.PermissionOverwrite(connect=False)},
                    reason="XERO Stats Channel"
                )
            except Exception as e:
                return await interaction.followup.send(embed=error_embed("Failed to Create Channel", str(e)))
        else:
            name = self._stats_channel_name(interaction.guild, stat)
            await channel.edit(name=name)

        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO stats_channels (guild_id, channel_id, stat_type) VALUES (?,?,?)",
                (interaction.guild.id, channel.id, stat)
            )
            await db.commit()

        embed = success_embed(
            "Stats Channel Created!",
            f"**Channel:** {channel.mention}\n"
            f"**Tracking:** {stat.replace('_',' ').title()}\n"
            f"**Updates:** Every 10 minutes automatically\n\n"
            f"*Members can't join this channel — it exists purely to show stats.*\n"
            f"*Create up to 7 different stat channels.*"
        )
        await interaction.followup.send(embed=embed)

    # ── /features stats-remove ─────────────────────────────────────────────
    @app_commands.command(name="stats-remove", description="Remove an auto-updating stats channel.")
    @app_commands.describe(stat="Which stat channel to remove")
    @app_commands.choices(stat=[
        app_commands.Choice(name="👥 Total Members",  value="members"),
        app_commands.Choice(name="🧑 Human Members",  value="humans"),
        app_commands.Choice(name="🤖 Bot Count",       value="bots"),
        app_commands.Choice(name="🟢 Online Members", value="online"),
        app_commands.Choice(name="💎 Boost Count",    value="boosts"),
        app_commands.Choice(name="📡 Channel Count",  value="channels"),
        app_commands.Choice(name="🎭 Role Count",     value="roles"),
    ])
    @app_commands.checks.has_permissions(manage_channels=True)
    async def stats_remove(self, interaction: discord.Interaction, stat: str):
        import aiosqlite
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT channel_id FROM stats_channels WHERE guild_id=? AND stat_type=?", (interaction.guild.id, stat)) as c:
                row = await c.fetchone()
            if row:
                ch = interaction.guild.get_channel(row[0])
                if ch:
                    try: await ch.delete(reason="XERO Stats Channel removed")
                    except Exception: pass
            await db.execute("DELETE FROM stats_channels WHERE guild_id=? AND stat_type=?", (interaction.guild.id, stat))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Stats Channel Removed", f"The **{stat}** stats channel has been deleted."))

    # ── /features bump-reminder ────────────────────────────────────────────
    @app_commands.command(name="bump-reminder", description="Set a bump reminder — XERO pings every 2 hours so you never forget to bump on Disboard.")
    @app_commands.describe(channel="Channel to send reminders", enabled="Enable or disable", ping_role="Role to ping with reminder")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def bump_reminder(self, interaction: discord.Interaction, channel: discord.TextChannel, enabled: bool = True, ping_role: discord.Role = None):
        import aiosqlite
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS bump_reminders (
                    guild_id INTEGER PRIMARY KEY, channel_id INTEGER,
                    enabled INTEGER DEFAULT 1, next_bump DATETIME
                )
            """)
            next_bump = (datetime.datetime.utcnow() + datetime.timedelta(hours=2)).strftime("%Y-%m-%d %H:%M:%S")
            await db.execute("""
                INSERT OR REPLACE INTO bump_reminders (guild_id, channel_id, enabled, next_bump)
                VALUES (?,?,?,?)
            """, (interaction.guild.id, channel.id, 1 if enabled else 0, next_bump))
            await db.commit()

        if ping_role:
            await self.bot.db.update_guild_setting(interaction.guild.id, "bump_role_id", ping_role.id)

        if enabled:
            await interaction.response.send_message(embed=success_embed(
                "Bump Reminder Set!",
                f"**Channel:** {channel.mention}\n"
                f"**Frequency:** Every 2 hours\n"
                f"**Ping:** {ping_role.mention if ping_role else 'No role'}\n\n"
                f"I'll remind your team to bump on Disboard and top.gg regularly.\n"
                f"*Consistent bumping = more members = bigger community.*"
            ))
        else:
            await interaction.response.send_message(embed=success_embed("Bump Reminder Disabled", "No more bump reminders."))

    # ── /features message-log ──────────────────────────────────────────────
    @app_commands.command(name="message-log", description="Log all edited and deleted messages to a channel. See everything, miss nothing.")
    @app_commands.describe(channel="Channel to send message logs", enabled="Enable or disable")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def message_log(self, interaction: discord.Interaction, channel: discord.TextChannel, enabled: bool = True):
        await self.bot.db.update_guild_setting(interaction.guild.id, "message_log_channel_id", channel.id if enabled else None)
        if enabled:
            await interaction.response.send_message(embed=success_embed(
                "Message Logger Enabled",
                f"**Log channel:** {channel.mention}\n\n"
                f"**Tracked:**\n"
                f"• ✏️ Message edits (shows before + after)\n"
                f"• 🗑️ Message deletes (shows full content)\n"
                f"• 🔇 Bulk message deletes\n\n"
                f"*Bot messages and system messages are excluded.*"
            ))
        else:
            await interaction.response.send_message(embed=success_embed("Message Logger Disabled", "Messages will no longer be logged."))

    # ── /features double-xp ────────────────────────────────────────────────
    @app_commands.command(name="double-xp", description="[Admin] Start a Double XP event — everyone earns 2× XP for the next X hours!")
    @app_commands.describe(hours="How many hours to run the event (1-24)")
    @app_commands.checks.has_permissions(administrator=True)
    async def double_xp(self, interaction: discord.Interaction, hours: int = 1):
        hours = max(1, min(24, hours))
        expires = datetime.datetime.now() + datetime.timedelta(hours=hours)
        DOUBLE_XP_EVENTS[interaction.guild.id] = expires

        # Announce in log channel
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        embed = discord.Embed(
            title="⚡  DOUBLE XP EVENT — NOW ACTIVE!",
            description=(
                f"For the next **{hours} hour(s)**, everyone earns **2× XP** for:\n"
                f"• Sending messages\n"
                f"• Using XERO commands\n\n"
                f"**Ends:** <t:{int(expires.timestamp())}:R>\n"
                f"Started by: {interaction.user.mention}"
            ),
            color=XERO.GOLD
        )
        embed.set_footer(text="XERO Double XP Event")

        log_ch = interaction.guild.get_channel(settings.get("log_channel_id") or settings.get("welcome_channel_id") or 0)
        if log_ch and log_ch != interaction.channel:
            try: await log_ch.send(embed=embed)
            except Exception: pass

        await interaction.response.send_message(embed=embed)
        logger.info(f"Double XP started in {interaction.guild.name} for {hours}h")

    # ── /features xp-blacklist ─────────────────────────────────────────────
    @app_commands.command(name="xp-blacklist", description="Stop XP being earned in specific channels (bot spam channels, etc.)")
    @app_commands.describe(channel="Channel to blacklist/whitelist", remove="Remove from blacklist instead")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def xp_blacklist(self, interaction: discord.Interaction, channel: discord.TextChannel, remove: bool = False):
        import aiosqlite
        async with self.bot.db._db_context() as db:
            await db.execute("CREATE TABLE IF NOT EXISTS xp_blacklist (guild_id INTEGER, channel_id INTEGER, PRIMARY KEY(guild_id, channel_id))")
            if remove:
                await db.execute("DELETE FROM xp_blacklist WHERE guild_id=? AND channel_id=?", (interaction.guild.id, channel.id))
                await db.commit()
                await interaction.response.send_message(embed=success_embed("Removed from XP Blacklist", f"{channel.mention} will now grant XP to members."))
            else:
                await db.execute("INSERT OR IGNORE INTO xp_blacklist (guild_id, channel_id) VALUES (?,?)", (interaction.guild.id, channel.id))
                await db.commit()
                await interaction.response.send_message(embed=success_embed("Channel XP Blacklisted", f"Members will **not** earn XP from messages in {channel.mention}.\n*Perfect for bot command channels.*"))

    # ── /features weekly ───────────────────────────────────────────────────
    @app_commands.command(name="weekly", description="Claim your weekly reward — 5× daily bonus + streak multiplier. Once per week.")
    async def weekly(self, interaction: discord.Interaction):
        import aiosqlite
        async with self.bot.db._db_context() as db:
            await db.execute("CREATE TABLE IF NOT EXISTS weekly_claims (user_id INTEGER, guild_id INTEGER, last_claim TEXT, PRIMARY KEY(user_id, guild_id))")
            async with db.execute("SELECT last_claim FROM weekly_claims WHERE user_id=? AND guild_id=?", (interaction.user.id, interaction.guild.id)) as c:
                row = await c.fetchone()

        now   = datetime.datetime.now(datetime.timezone.utc)
        if row and row[0]:
            last = datetime.datetime.fromisoformat(row[0])
            if last.tzinfo is None:
                last = last.replace(tzinfo=datetime.timezone.utc)
            since = (now - last).total_seconds()
            if since < 604800:  # 7 days
                next_ts = int((last + datetime.timedelta(weeks=1)).timestamp())
                return await interaction.response.send_message(embed=error_embed(
                    "Already Claimed!",
                    f"Next weekly: <t:{next_ts}:R>\n"
                    f"*(Once per week — Sundays are a great day to claim!)*"
                ))

        # Calculate reward
        streak = await self.bot.db.get_streak(interaction.user.id, interaction.guild.id)
        s      = streak.get("daily_streak", 0)
        mult   = min(1.0 + max(0, s-1)*0.05, 3.0)  # streak multiplier
        base   = 25000  # 5× daily base
        bonus  = random.randint(0, 10000)
        total  = int((base + bonus) * mult)

        await self.bot.db.update_economy(interaction.user.id, interaction.guild.id, wallet_delta=total, earned_delta=total)
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO weekly_claims (user_id, guild_id, last_claim) VALUES (?,?,?)",
                (interaction.user.id, interaction.guild.id, now.isoformat())
            )
            await db.commit()

        embed = comprehensive_embed(title="🗓️  Weekly Reward Claimed!", color=XERO.GOLD)
        embed.set_thumbnail(url=interaction.user.display_avatar.url)
        embed.add_field(name="💰 Reward",      value=f"**${total:,}**",        inline=True)
        embed.add_field(name="⚡ Multiplier",  value=f"**{mult:.2f}×**",        inline=True)
        embed.add_field(name="🔥 Streak",      value=f"**{s} days**",           inline=True)
        embed.add_field(name="📊 Breakdown",   value=f"Base ${base:,} + Bonus ${bonus:,} × {mult:.2f}", inline=False)
        embed.set_footer(text="XERO Economy  •  Come back next week!")
        await interaction.response.send_message(embed=embed)



async def setup(bot):
    await bot.add_cog(ServerFeatures(bot))
