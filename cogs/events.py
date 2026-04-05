"""
XERO Bot — Events v2
Handles: welcome/farewell, XP, reminders, starboard, temp voice, birthdays,
AFK, automod (via main.py), security listeners, AI mentions, milestones.

Security listeners added:
  - on_guild_role_update      → permission escalation watchdog
  - on_webhooks_update        → webhook protection
  - on_member_join (bots)     → bot protection + alt scoring + raid mode
  - on_guild_channel_delete   → anti-nuke tracking
  - on_guild_channel_create   → anti-nuke tracking (mass channel creation)
  - on_guild_role_delete      → anti-nuke tracking
  - on_member_ban             → anti-nuke tracking
  - on_raw_bulk_message_delete → anti-nuke tracking
  - on_guild_emojis_update    → anti-nuke tracking (mass emoji delete)
  - on_member_remove          → role save for role-restore
"""
import discord
from discord.ext import commands, tasks
import logging, random, re, datetime, aiosqlite, asyncio
from utils.embeds import XERO, comprehensive_embed, brand_embed

logger = logging.getLogger("XERO.Events")

AI_MEMORY: dict = {}   # guild_id -> [{role, content}]

# Dangerous permissions that trigger the watchdog
DANGEROUS_PERMS = {"administrator", "ban_members", "manage_guild",
                   "manage_roles", "kick_members", "manage_channels"}


class Events(commands.Cog):
    def __init__(self, bot):
        self.bot = bot
        self.xp_cooldowns: dict = {}
        self.process_reminders.start()
        self.process_temp_bans.start()
        self.check_birthdays.start()
        self.process_scheduled_messages.start()
        self.check_raid_mode_expiry.start()

    def cog_unload(self):
        self.process_reminders.cancel()
        self.process_temp_bans.cancel()
        self.check_birthdays.cancel()
        self.process_scheduled_messages.cancel()
        self.check_raid_mode_expiry.cancel()

    # ══════════════════════════════════════════════════════════════════════
    # BACKGROUND TASKS
    # ══════════════════════════════════════════════════════════════════════

    @tasks.loop(seconds=30)
    async def process_reminders(self):
        try:
            reminders = await self.bot.db.get_due_reminders()
            for r in reminders:
                try:
                    embed = discord.Embed(
                        title="⏰  Reminder!",
                        description=r["message"],
                        color=XERO.PRIMARY,
                        timestamp=discord.utils.utcnow()
                    )
                    embed.set_footer(text=f"Reminder #{r['id']}  •  XERO Bot")

                    channel = self.bot.get_channel(r["channel_id"])
                    user    = self.bot.get_user(r["user_id"])
                    if not user:
                        try: user = await self.bot.fetch_user(r["user_id"])
                        except Exception: pass

                    if channel and user:
                        try: await channel.send(content=user.mention, embed=embed)
                        except Exception as e: logger.warning(f"Reminder channel: {e}")

                    if user:
                        try:
                            dm_embed = discord.Embed(
                                title="⏰  Your Reminder",
                                description=r["message"],
                                color=XERO.PRIMARY,
                                timestamp=discord.utils.utcnow()
                            )
                            dm_embed.set_footer(text="You set this with XERO Bot")
                            await user.send(embed=dm_embed)
                        except discord.Forbidden: pass
                        except Exception as e: logger.warning(f"Reminder DM: {e}")

                    await self.bot.db.mark_reminder_sent(r["id"])
                except Exception as e:
                    logger.error(f"Reminder item: {e}")
        except Exception as e:
            logger.error(f"Reminder loop: {e}")

    @process_reminders.before_loop
    async def before_reminders(self): await self.bot.wait_until_ready()

    @tasks.loop(minutes=5)
    async def process_temp_bans(self):
        try:
            async with self.bot.db._db_context() as db:
                try:
                    async with db.execute(
                        "SELECT case_id, guild_id, user_id, reason "
                        "FROM temp_bans WHERE expires_at <= datetime('now')"
                    ) as c:
                        due = await c.fetchall()
                    for case_id, guild_id, user_id, reason in due:
                        guild = self.bot.get_guild(guild_id)
                        if guild:
                            try:
                                await guild.unban(
                                    discord.Object(user_id),
                                    reason=f"XERO TempBan expired: {reason}"
                                )
                            except Exception: pass
                        await db.execute("DELETE FROM temp_bans WHERE case_id=?", (case_id,))
                    await db.commit()
                except Exception: pass
        except Exception as e:
            logger.debug(f"Temp-ban loop: {e}")

    @process_temp_bans.before_loop
    async def before_temp_bans(self): await self.bot.wait_until_ready()

    @tasks.loop(hours=1)
    async def check_birthdays(self):
        today = datetime.date.today()
        for guild in self.bot.guilds:
            try:
                settings = await self.bot.db.get_guild_settings(guild.id)
                ch_id = settings.get("birthday_channel_id") or settings.get("welcome_channel_id")
                if not ch_id: continue
                ch = guild.get_channel(ch_id)
                if not ch: continue
                async with self.bot.db._db_context() as db:
                    db.row_factory = aiosqlite.Row
                    async with db.execute(
                        "SELECT * FROM birthdays WHERE guild_id=? AND month=? AND day=? "
                        "AND announced_year!=?",
                        (guild.id, today.month, today.day, today.year)
                    ) as c:
                        bdays = [dict(r) for r in await c.fetchall()]
                for b in bdays:
                    m = guild.get_member(b["user_id"])
                    if not m: continue
                    age = (f" They're turning **{today.year - b['year']}**!"
                           if b.get("year") else "")
                    embed = discord.Embed(
                        title="🎂  Happy Birthday!",
                        description=f"Everyone wish {m.mention} a happy birthday! 🎉{age}",
                        color=discord.Color.pink()
                    )
                    embed.set_thumbnail(url=m.display_avatar.url)
                    await ch.send(content=m.mention, embed=embed)
                    async with self.bot.db._db_context() as db:
                        await db.execute(
                            "UPDATE birthdays SET announced_year=? WHERE user_id=? AND guild_id=?",
                            (today.year, b["user_id"], guild.id)
                        )
                        await db.commit()
            except Exception as e:
                logger.error(f"Birthday {guild.name}: {e}")

    @check_birthdays.before_loop
    async def before_birthdays(self): await self.bot.wait_until_ready()

    @tasks.loop(minutes=1)
    async def process_scheduled_messages(self):
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM scheduled_messages "
                    "WHERE sent=0 AND send_at<=datetime('now')"
                ) as c:
                    due = [dict(r) for r in await c.fetchall()]
            for msg in due:
                try:
                    ch = self.bot.get_channel(msg["channel_id"])
                    if ch:
                        if msg.get("embed_title"):
                            embed = discord.Embed(
                                title=msg["embed_title"],
                                description=msg.get("message", ""),
                                color=XERO.PRIMARY
                            )
                            await ch.send(embed=embed)
                        else:
                            await ch.send(msg["message"])
                    async with self.bot.db._db_context() as db:
                        if msg.get("repeat_hours", 0) > 0:
                            nxt = (datetime.datetime.now() +
                                   datetime.timedelta(hours=msg["repeat_hours"])).isoformat()
                            await db.execute(
                                "UPDATE scheduled_messages SET send_at=? WHERE id=?",
                                (nxt, msg["id"])
                            )
                        else:
                            await db.execute(
                                "UPDATE scheduled_messages SET sent=1 WHERE id=?", (msg["id"],)
                            )
                        await db.commit()
                except Exception as e:
                    logger.error(f"Scheduled msg: {e}")
        except Exception as e:
            logger.error(f"Scheduled loop: {e}")

    @process_scheduled_messages.before_loop
    async def before_scheduled(self): await self.bot.wait_until_ready()

    @tasks.loop(minutes=5)
    async def check_raid_mode_expiry(self):
        """Auto-disable raid mode when it expires."""
        try:
            for guild in self.bot.guilds:
                try:
                    settings = await self.bot.db.get_guild_settings(guild.id)
                    if not settings.get("raid_mode_enabled"):
                        continue
                    until_str = settings.get("raid_mode_until")
                    if not until_str:
                        continue
                    until = datetime.datetime.fromisoformat(str(until_str))
                    if datetime.datetime.now() >= until:
                        security = self.bot.cogs.get("Security")
                        if security:
                            await security._disable_raid_mode(guild)
                            logger.info(f"Raid mode auto-expired for {guild.name}")
                except Exception:
                    pass
        except Exception as e:
            logger.debug(f"Raid mode expiry: {e}")

    @check_raid_mode_expiry.before_loop
    async def before_raid_check(self): await self.bot.wait_until_ready()

    # ══════════════════════════════════════════════════════════════════════
    # GUILD EVENTS
    # ══════════════════════════════════════════════════════════════════════

    @commands.Cog.listener()
    async def on_guild_join(self, guild: discord.Guild):
        await self.bot.db.create_guild_settings(guild.id)
        logger.info(f"Joined: {guild.name} ({guild.id})")
        if (guild.system_channel and
                guild.system_channel.permissions_for(guild.me).send_messages):
            embed = discord.Embed(
                title="👋  Hey, I'm XERO!",
                description=(
                    "Thanks for adding me! Use `/admin` for the full control panel.\n\n"
                    "**300+ commands** — AI, Moderation, Economy, Levels, Giveaways, "
                    "Music, Tickets + more.\nAll premium features. Completely free."
                ),
                color=XERO.PRIMARY
            )
            embed.set_thumbnail(url=self.bot.user.display_avatar.url)
            try: await guild.system_channel.send(embed=embed)
            except Exception: pass

    @commands.Cog.listener()
    async def on_guild_remove(self, guild: discord.Guild):
        logger.info(f"Left: {guild.name} ({guild.id})")

    # ══════════════════════════════════════════════════════════════════════
    # SECURITY LISTENERS
    # ══════════════════════════════════════════════════════════════════════

    @commands.Cog.listener()
    async def on_guild_role_update(self, before: discord.Role, after: discord.Role):
        """Permission escalation watchdog — catch unauthorized admin grants."""
        try:
            guild    = after.guild
            settings = await self.bot.db.get_guild_settings(guild.id)
            if not settings.get("perm_watchdog_enabled", 1):
                return
            if not settings.get("anti_nuke_enabled", 0):
                return

            # Find which permissions were added
            before_perms = set(name for name, val in before.permissions if val)
            after_perms  = set(name for name, val in after.permissions if val)
            added_perms  = after_perms - before_perms
            danger_added = added_perms & DANGEROUS_PERMS

            if not danger_added:
                return

            # Find who made this change via audit log
            await asyncio.sleep(1)  # small delay for audit log to populate
            try:
                actor = None
                async for entry in guild.audit_logs(
                    limit=5, action=discord.AuditLogAction.role_update
                ):
                    if entry.target.id == after.id:
                        actor = entry.user
                        break
            except Exception:
                actor = None

            if not actor:
                return
            # Owner is always allowed
            if actor.id == guild.owner_id:
                return
            # If actor has admin already that's their existing permission — only flag if
            # they just gave themselves a role with new dangerous perms
            member = guild.get_member(actor.id)
            if not member:
                return

            # Trigger anti-nuke for permission escalation
            security = self.bot.cogs.get("Security")
            if security:
                await security.track_nuke_action(guild, member, "permission_escalate")

            # Log it immediately
            log_ch = guild.get_channel(settings.get("log_channel_id") or 0)
            if log_ch:
                embed = discord.Embed(
                    title="⚠️  Permission Escalation Detected",
                    description=(
                        f"**{actor.mention}** modified role **{after.name}**\n"
                        f"**Added permissions:** `{'`, `'.join(danger_added)}`"
                    ),
                    color=discord.Color.orange(),
                    timestamp=discord.utils.utcnow()
                )
                embed.set_footer(text="XERO Permission Watchdog")
                try: await log_ch.send(embed=embed)
                except Exception: pass
        except Exception as e:
            logger.error(f"on_guild_role_update: {e}")

    @commands.Cog.listener()
    async def on_webhooks_update(self, channel: discord.TextChannel):
        """Webhook protection — delete rogue webhooks instantly."""
        try:
            guild    = channel.guild
            settings = await self.bot.db.get_guild_settings(guild.id)
            if not settings.get("webhook_protection_enabled", 1):
                return

            await asyncio.sleep(1)  # let audit log populate

            # Find who created a webhook recently
            try:
                actor = None
                webhook_id = None
                async for entry in guild.audit_logs(
                    limit=5, action=discord.AuditLogAction.webhook_create
                ):
                    actor      = entry.user
                    webhook_id = entry.target.id if entry.target else None
                    break
            except Exception:
                return

            if not actor:
                return

            # Allow if actor is admin or owner
            member = guild.get_member(actor.id)
            if member and (member.guild_permissions.administrator or
                           member.id == guild.owner_id):
                return

            # Non-admin created a webhook — delete it immediately
            try:
                webhooks = await channel.webhooks()
                for wh in webhooks:
                    if wh.user and wh.user.id == actor.id:
                        await wh.delete(reason="XERO Webhook Protection: non-admin creator")
                        logger.warning(
                            f"Webhook protection: deleted webhook by {actor} in {guild.name}"
                        )
            except Exception as e:
                logger.warning(f"Webhook delete failed: {e}")

            # Log the attempt
            log_ch = guild.get_channel(settings.get("log_channel_id") or 0)
            if log_ch:
                embed = discord.Embed(
                    title="🪝  Rogue Webhook Blocked",
                    description=(
                        f"**{actor.mention}** (`{actor.id}`) attempted to create a webhook "
                        f"in {channel.mention} without admin permissions.\n\n"
                        f"**Webhook deleted immediately.** This is a common phishing attack vector."
                    ),
                    color=discord.Color.red(),
                    timestamp=discord.utils.utcnow()
                )
                embed.set_footer(text="XERO Webhook Protection")
                try: await log_ch.send(embed=embed)
                except Exception: pass

            # Trigger anti-nuke tracking
            if member:
                security = self.bot.cogs.get("Security")
                if security:
                    await security.track_nuke_action(guild, member, "webhook_create")
        except Exception as e:
            logger.error(f"on_webhooks_update: {e}")

    @commands.Cog.listener()
    async def on_guild_channel_delete(self, channel: discord.abc.GuildChannel):
        """Anti-nuke: track mass channel deletion."""
        try:
            guild = channel.guild
            await asyncio.sleep(0.5)
            try:
                actor = None
                async for entry in guild.audit_logs(
                    limit=3, action=discord.AuditLogAction.channel_delete
                ):
                    actor = entry.user
                    break
            except Exception:
                return
            if not actor or actor.id == self.bot.user.id:
                return
            member = guild.get_member(actor.id)
            if not member or member.id == guild.owner_id:
                return
            security = self.bot.cogs.get("Security")
            if security:
                await security.track_nuke_action(guild, member, "channel_delete")
        except Exception as e:
            logger.error(f"on_guild_channel_delete: {e}")

    @commands.Cog.listener()
    async def on_guild_channel_create(self, channel: discord.abc.GuildChannel):
        """Anti-nuke: track mass channel creation (also a nuke pattern)."""
        try:
            guild = channel.guild
            await asyncio.sleep(0.5)
            try:
                actor = None
                async for entry in guild.audit_logs(
                    limit=3, action=discord.AuditLogAction.channel_create
                ):
                    actor = entry.user
                    break
            except Exception:
                return
            if not actor or actor.id == self.bot.user.id:
                return
            member = guild.get_member(actor.id)
            if not member or member.id == guild.owner_id:
                return
            security = self.bot.cogs.get("Security")
            if security:
                await security.track_nuke_action(guild, member, "channel_create")
        except Exception as e:
            logger.error(f"on_guild_channel_create: {e}")

    @commands.Cog.listener()
    async def on_guild_role_delete(self, role: discord.Role):
        """Anti-nuke: track mass role deletion."""
        try:
            guild = role.guild
            await asyncio.sleep(0.5)
            try:
                actor = None
                async for entry in guild.audit_logs(
                    limit=3, action=discord.AuditLogAction.role_delete
                ):
                    actor = entry.user
                    break
            except Exception:
                return
            if not actor or actor.id == self.bot.user.id:
                return
            member = guild.get_member(actor.id)
            if not member or member.id == guild.owner_id:
                return
            security = self.bot.cogs.get("Security")
            if security:
                await security.track_nuke_action(guild, member, "role_delete")
        except Exception as e:
            logger.error(f"on_guild_role_delete: {e}")

    @commands.Cog.listener()
    async def on_member_ban(self, guild: discord.Guild, user: discord.User):
        """Anti-nuke: track mass bans."""
        try:
            await asyncio.sleep(0.5)
            try:
                actor = None
                async for entry in guild.audit_logs(
                    limit=3, action=discord.AuditLogAction.ban
                ):
                    actor = entry.user
                    break
            except Exception:
                return
            if not actor or actor.id == self.bot.user.id:
                return
            member = guild.get_member(actor.id)
            if not member or member.id == guild.owner_id:
                return
            security = self.bot.cogs.get("Security")
            if security:
                await security.track_nuke_action(guild, member, "mass_ban")
        except Exception as e:
            logger.error(f"on_member_ban: {e}")

    @commands.Cog.listener()
    async def on_raw_bulk_message_delete(self, payload: discord.RawBulkMessageDeleteEvent):
        """Anti-nuke: track bulk message deletion."""
        try:
            guild = self.bot.get_guild(payload.guild_id)
            if not guild:
                return
            settings = await self.bot.db.get_guild_settings(guild.id)
            if not settings.get("anti_nuke_enabled", 0):
                return
            await asyncio.sleep(0.5)
            try:
                actor = None
                async for entry in guild.audit_logs(
                    limit=3, action=discord.AuditLogAction.message_bulk_delete
                ):
                    actor = entry.user
                    break
            except Exception:
                return
            if not actor or actor.id == self.bot.user.id:
                return
            member = guild.get_member(actor.id)
            if not member or member.id == guild.owner_id:
                return
            security = self.bot.cogs.get("Security")
            if security:
                await security.track_nuke_action(guild, member, "message_bulk_delete")
        except Exception as e:
            logger.error(f"on_raw_bulk_message_delete: {e}")

    @commands.Cog.listener()
    async def on_guild_emojis_update(self, guild: discord.Guild,
                                     before: list, after: list):
        """Anti-nuke: track mass emoji deletion."""
        try:
            deleted = len(before) - len(after)
            if deleted < 3:
                return
            settings = await self.bot.db.get_guild_settings(guild.id)
            if not settings.get("anti_nuke_enabled", 0):
                return
            await asyncio.sleep(0.5)
            try:
                actor = None
                async for entry in guild.audit_logs(
                    limit=3, action=discord.AuditLogAction.emoji_delete
                ):
                    actor = entry.user
                    break
            except Exception:
                return
            if not actor or actor.id == self.bot.user.id:
                return
            member = guild.get_member(actor.id)
            if not member or member.id == guild.owner_id:
                return
            security = self.bot.cogs.get("Security")
            if security:
                await security.track_nuke_action(guild, member, "emoji_delete")
        except Exception as e:
            logger.error(f"on_guild_emojis_update: {e}")

    # ══════════════════════════════════════════════════════════════════════
    # MEMBER JOIN
    # ══════════════════════════════════════════════════════════════════════

    @commands.Cog.listener()
    async def on_member_join(self, member: discord.Member):
        settings = await self.bot.db.get_guild_settings(member.guild.id)
        if not settings:
            return

        # ── Bot protection ─────────────────────────────────────────────
        if member.bot:
            try:
                if settings.get("bot_protection_enabled", 0):
                    await asyncio.sleep(1)
                    try:
                        actor = None
                        async for entry in member.guild.audit_logs(
                            limit=5, action=discord.AuditLogAction.bot_add
                        ):
                            if entry.target.id == member.id:
                                actor = entry.user
                                break
                    except Exception:
                        actor = None

                    if actor:
                        authorizer = member.guild.get_member(actor.id)
                        if authorizer and not authorizer.guild_permissions.manage_guild:
                            # Kick the unauthorized bot
                            try:
                                await member.kick(
                                    reason=f"XERO Bot Protection: added by {actor} "
                                           f"without Manage Server permission"
                                )
                                logger.warning(
                                    f"Bot protection: kicked {member} added by {actor} in {member.guild.name}"
                                )
                            except Exception as e:
                                logger.error(f"Bot kick failed: {e}")

                            log_ch = member.guild.get_channel(
                                settings.get("log_channel_id") or 0
                            )
                            if log_ch:
                                embed = discord.Embed(
                                    title="🤖  Unauthorized Bot Blocked",
                                    description=(
                                        f"Bot **{member}** was added by {actor.mention} "
                                        f"who lacks **Manage Server** permission.\n\n"
                                        f"Bot has been **kicked**."
                                    ),
                                    color=discord.Color.red(),
                                    timestamp=discord.utils.utcnow()
                                )
                                try: await log_ch.send(embed=embed)
                                except Exception: pass

                            # Alert all admins
                            for m in member.guild.members:
                                if m.guild_permissions.administrator and not m.bot:
                                    try: await m.send(embed=discord.Embed(
                                        title="🤖  Unauthorized Bot Addition Blocked",
                                        description=(
                                            f"Someone tried to add bot **{member}** to "
                                            f"**{member.guild.name}** without permission.\n"
                                            f"Authorizer: {actor.mention}\nBot was kicked."
                                        ),
                                        color=discord.Color.red()
                                    ))
                                    except Exception: pass
            except Exception as e:
                logger.error(f"Bot protection on_member_join: {e}")
            return  # Don't process bots further

        # ── Raid mode: kick underage accounts ─────────────────────────
        if settings.get("raid_mode_enabled", 0):
            min_age = settings.get("raid_mode_min_age_days", 7)
            age_days = (discord.utils.utcnow() - member.created_at).days
            if age_days < min_age:
                try:
                    await member.send(embed=discord.Embed(
                        title=f"🚫 Entry Denied — {member.guild.name}",
                        description=(
                            f"This server is currently in **Raid Mode**.\n"
                            f"Accounts under **{min_age} days old** are not permitted.\n"
                            f"Your account is **{age_days} days old**. Please try later."
                        ),
                        color=discord.Color.red()
                    ))
                except Exception:
                    pass
                try:
                    await member.kick(reason=f"XERO Raid Mode: account {age_days}d < {min_age}d minimum")
                except Exception as e:
                    logger.error(f"Raid mode kick: {e}")
                return

        # ── Alt account scoring ────────────────────────────────────────
        try:
            security = self.bot.cogs.get("Security")
            if security:
                await security.check_alt_score(member)
        except Exception as e:
            logger.error(f"Alt score: {e}")

        # ── Account age filter ─────────────────────────────────────────
        min_age = settings.get("min_account_age_days", 0)
        if min_age > 0:
            age_days = (discord.utils.utcnow() - member.created_at).days
            if age_days < min_age:
                action = settings.get("account_age_action", "kick_dm")
                try:
                    if "dm" in action:
                        await member.send(embed=discord.Embed(
                            title=f"❌ Account Too New — {member.guild.name}",
                            description=(
                                f"Your account must be at least **{min_age} days old** "
                                f"to join this server.\n"
                                f"Your account is **{age_days} days old**. Please try later."
                            ),
                            color=discord.Color.red()
                        ))
                    if "ban" in action:
                        await member.ban(
                            reason=f"XERO Account Age: {age_days}d < {min_age}d minimum"
                        )
                    else:
                        await member.kick(
                            reason=f"XERO Account Age: {age_days}d < {min_age}d minimum"
                        )
                    return
                except Exception as e:
                    logger.error(f"Account age filter: {e}")

        # ── Role restore ───────────────────────────────────────────────
        if settings.get("role_restore_enabled", 0):
            try:
                async with self.bot.db._db_context() as db:
                    async with db.execute(
                        "SELECT role_ids FROM member_roles WHERE user_id=? AND guild_id=?",
                        (member.id, member.guild.id)
                    ) as c:
                        row = await c.fetchone()
                if row and row[0]:
                    role_ids = [int(r) for r in row[0].split(",") if r.strip()]
                    roles = [member.guild.get_role(rid) for rid in role_ids]
                    roles = [r for r in roles
                             if r and not r.managed and r != member.guild.default_role]
                    if roles:
                        await member.add_roles(*roles, reason="XERO Role Restore")
            except Exception as e:
                logger.error(f"Role restore: {e}")

        # ── Raid detection (SmartMod) ──────────────────────────────────
        try:
            smart = self.bot.cogs.get("SmartMod")
            if smart:
                await smart.handle_member_join_check(member)
        except Exception:
            pass

        # ── Auto-role ──────────────────────────────────────────────────
        if settings.get("autorole_id"):
            role = member.guild.get_role(settings["autorole_id"])
            if role:
                try: await member.add_roles(role, reason="XERO Auto-Role")
                except Exception as e: logger.error(f"Auto-role: {e}")

        # ── Welcome message ────────────────────────────────────────────
        ch = None
        if settings.get("welcome_channel_id"):
            ch = self.bot.get_channel(settings["welcome_channel_id"])
            if not ch:
                try: ch = await self.bot.fetch_channel(settings["welcome_channel_id"])
                except Exception: ch = None

            if ch:
                try:
                    raw = (settings.get("welcome_message") or
                           "Welcome {user} to **{server}**! You are member #{count}. 🎉")
                    msg = (raw
                           .replace("{user}",   member.mention)
                           .replace("{name}",   member.display_name)
                           .replace("{server}", member.guild.name)
                           .replace("{count}",  str(member.guild.member_count)))

                    embed = discord.Embed(
                        title=f"👋  Welcome to {member.guild.name}!",
                        description=msg,
                        color=XERO.PRIMARY
                    )
                    embed.set_thumbnail(url=member.display_avatar.url)
                    embed.add_field(name="👥  Member #",
                                    value=f"**{member.guild.member_count:,}**", inline=True)
                    embed.add_field(name="📅  Account",
                                    value=f"<t:{int(member.created_at.timestamp())}:R>", inline=True)
                    embed.set_footer(text="Welcome!")

                    file       = None
                    use_brand  = settings.get("welcome_use_brand", 1)
                    custom_img = settings.get("welcome_custom_image")

                    if use_brand:
                        try:
                            embed, file = await brand_embed(embed, member.guild, self.bot)
                        except Exception:
                            pass
                    elif custom_img:
                        embed.set_image(url=custom_img)

                    unified = settings.get("unified_image_url")
                    if unified and not embed.image:
                        embed.set_image(url=unified)

                    if file:
                        await ch.send(embed=embed, file=file)
                    else:
                        await ch.send(embed=embed)
                except Exception as e:
                    logger.error(f"Welcome: {e}")

        # ── Personality welcome ────────────────────────────────────────
        try:
            personality = self.bot.cogs.get("Personality")
            if personality and settings.get("personality_enabled", 1):
                await personality.on_member_welcome(member, ch)
        except Exception:
            pass

    # ══════════════════════════════════════════════════════════════════════
    # MEMBER REMOVE
    # ══════════════════════════════════════════════════════════════════════

    @commands.Cog.listener()
    async def on_member_remove(self, member: discord.Member):
        if member.bot:
            return
        settings = await self.bot.db.get_guild_settings(member.guild.id)
        if not settings:
            return

        # ── Save roles for role-restore ────────────────────────────────
        if settings.get("role_restore_enabled", 0):
            try:
                saveable = [
                    r for r in member.roles
                    if not r.managed and r != member.guild.default_role
                ]
                if saveable:
                    role_ids = ",".join(str(r.id) for r in saveable)
                    async with self.bot.db._db_context() as db:
                        await db.execute("""
                            INSERT INTO member_roles (user_id, guild_id, role_ids, saved_at)
                            VALUES (?,?,?,datetime('now'))
                            ON CONFLICT(user_id, guild_id) DO UPDATE SET
                                role_ids=excluded.role_ids,
                                saved_at=excluded.saved_at
                        """, (member.id, member.guild.id, role_ids))
                        await db.commit()
            except Exception as e:
                logger.error(f"Role save on leave: {e}")

        # ── Farewell message ───────────────────────────────────────────
        if settings.get("farewell_channel_id"):
            ch = self.bot.get_channel(settings["farewell_channel_id"])
            if ch:
                try:
                    raw = (settings.get("farewell_message") or
                           "Goodbye {name}, we'll miss you!")
                    msg = (raw
                           .replace("{user}",   member.mention)
                           .replace("{name}",   member.display_name)
                           .replace("{server}", member.guild.name))
                    embed = discord.Embed(
                        description=msg,
                        color=discord.Color(0x5865F2)
                    )
                    embed.set_thumbnail(url=member.display_avatar.url)
                    await ch.send(embed=embed)
                except Exception as e:
                    logger.error(f"Farewell: {e}")


    # ══════════════════════════════════════════════════════════════════════
    # ON MESSAGE — XP, AFK, Counting, Highlights
    # ══════════════════════════════════════════════════════════════════════

    @commands.Cog.listener()
    async def on_message(self, message: discord.Message):
        if message.author.bot or not message.guild:
            return

        guild_id = message.guild.id
        user_id  = message.author.id
        now      = datetime.datetime.utcnow()

        # ── AutoMod: must run FIRST, returns True if message was deleted ──
        try:
            automod = self.bot.cogs.get("AegisAutoMod")
            if automod:
                triggered = await automod.process_message(message)
                if triggered:
                    return
        except Exception as _ame:
            logger.debug(f"AutoMod dispatch: {_ame}")

        # ── AI on @mention ────────────────────────────────────────────────
        try:
            if self.bot.user in message.mentions and not message.mention_everyone:
                _s = await self.bot.db.get_guild_settings(guild_id)
                if _s and _s.get("ai_enabled", 1):
                    _raw = message.content.replace(f"<@{self.bot.user.id}>","").replace(f"<@!{self.bot.user.id}>","").strip()
                    if _raw:
                        async with message.channel.typing():
                            _resp = await self.bot.nvidia.ask(_raw)
                            if _resp:
                                for _chunk in [_resp[i:i+1990] for i in range(0,len(_resp),1990)]:
                                    await message.reply(_chunk)
        except Exception as _aie:
            logger.debug(f"AI mention: {_aie}")

        settings = await self.bot.db.get_guild_settings(guild_id)

        # ── AFK: clear AFK if user is back ────────────────────────────
        try:
            afk_data = await self.bot.db.get_afk(user_id, guild_id)
            if afk_data:
                await self.bot.db.remove_afk(user_id, guild_id)
                try:
                    afk_embed = discord.Embed(
                        description=f"👋 Welcome back {message.author.mention}! Your AFK status has been removed.",
                        color=XERO.PRIMARY
                    )
                    sent = await message.channel.send(embed=afk_embed)
                    await asyncio.sleep(5)
                    try: await sent.delete()
                    except Exception: pass
                except Exception: pass
        except Exception as e:
            logger.debug(f"AFK clear: {e}")

        # ── AFK: notify if mentioned AFK user ─────────────────────────
        try:
            for mention in message.mentions:
                if mention.bot or mention.id == user_id:
                    continue
                afk_data = await self.bot.db.get_afk(mention.id, guild_id)
                if afk_data:
                    reason = afk_data.get("reason") or "No reason set"
                    afk_embed = discord.Embed(
                        description=f"💤 {mention.display_name} is AFK: **{reason}**",
                        color=XERO.PRIMARY
                    )
                    try:
                        sent = await message.channel.send(embed=afk_embed)
                        await asyncio.sleep(8)
                        try: await sent.delete()
                        except Exception: pass
                    except Exception: pass
        except Exception as e:
            logger.debug(f"AFK mention: {e}")

        # ── Counting channel ──────────────────────────────────────────
        try:
            await self._handle_counting(message, guild_id, user_id)
        except Exception as e:
            logger.debug(f"Counting: {e}")

        # ── XP / Leveling ─────────────────────────────────────────────
        try:
            if settings.get("leveling_enabled", 1):
                # 60-second cooldown per user per guild
                cooldown_key = f"{guild_id}:{user_id}"
                last = self.xp_cooldowns.get(cooldown_key)
                if last is None or (now - last).total_seconds() >= 60:
                    self.xp_cooldowns[cooldown_key] = now
                    xp_gain = random.randint(15, 40)

                    # Double XP check (server_features)
                    server_features = self.bot.cogs.get("ServerFeatures")
                    if server_features and server_features.is_double_xp(guild_id):
                        xp_gain *= 2

                    leveled_up, new_level = await self.bot.db.update_xp(user_id, guild_id, xp_gain)

                    if leveled_up:
                        await self._handle_level_up(message, new_level, settings)
        except Exception as e:
            logger.debug(f"XP award: {e}")

    async def _handle_counting(self, message: discord.Message, guild_id: int, user_id: int):
        """Handle counting channel logic."""
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM counting_config WHERE guild_id=? AND enabled=1",
                    (guild_id,)
                ) as c:
                    cfg = await c.fetchone()
        except Exception:
            return

        if not cfg:
            return
        cfg = dict(cfg)

        if message.channel.id != cfg["channel_id"]:
            return

        content = message.content.strip()
        try:
            number = int(content)
        except ValueError:
            # Non-number in counting channel → delete and warn
            try:
                await message.delete()
            except Exception:
                pass
            try:
                warn = await message.channel.send(
                    f"{message.author.mention} Only numbers allowed here! Count is at **{cfg['current']}**.",
                    delete_after=5
                )
            except Exception:
                pass
            return

        expected = cfg["current"] + 1

        # Same user counting twice in a row
        if user_id == cfg.get("last_user_id") and cfg["current"] > 0:
            try:
                await message.delete()
            except Exception:
                pass
            try:
                await message.channel.send(
                    f"{message.author.mention} You can't count twice in a row! Count reset to **0**. 💥",
                    delete_after=8
                )
            except Exception:
                pass
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "UPDATE counting_config SET current=0, last_user_id=NULL WHERE guild_id=? AND channel_id=?",
                    (guild_id, cfg["channel_id"])
                )
                await db.commit()
            return

        if number == expected:
            # Correct!
            new_high = max(cfg.get("high_score", 0), number)
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "UPDATE counting_config SET current=?, last_user_id=?, high_score=? WHERE guild_id=? AND channel_id=?",
                    (number, user_id, new_high, guild_id, cfg["channel_id"])
                )
                await db.commit()
            try:
                await message.add_reaction("✅")
            except Exception:
                pass
            if number == new_high and number % 10 == 0:
                try:
                    await message.channel.send(
                        f"🎉 New high score: **{number}**! Keep going!",
                        delete_after=10
                    )
                except Exception:
                    pass
        else:
            # Wrong number — reset
            try:
                await message.delete()
            except Exception:
                pass
            try:
                await message.channel.send(
                    f"{message.author.mention} **{number}** is wrong! Expected **{expected}**. Count reset to **0**. 💥",
                    delete_after=8
                )
            except Exception:
                pass
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "UPDATE counting_config SET current=0, last_user_id=NULL WHERE guild_id=? AND channel_id=?",
                    (guild_id, cfg["channel_id"])
                )
                await db.commit()

    async def _handle_level_up(self, message: discord.Message, new_level: int, settings: dict):
        """Send level-up notification and assign rewards."""
        try:
            # Level-up channel or current channel
            ch_id = settings.get("level_up_channel_id")
            ch = message.guild.get_channel(ch_id) if ch_id else message.channel

            if ch:
                embed = discord.Embed(
                    title="🎉 Level Up!",
                    description=(
                        f"{message.author.mention} reached **Level {new_level}**! 🚀\n"
                        f"Keep chatting to level up further!"
                    ),
                    color=discord.Color(0x5865F2),
                    timestamp=discord.utils.utcnow()
                )
                embed.set_thumbnail(url=message.author.display_avatar.url)
                embed.set_footer(text="XERO Levels")
                try:
                    await ch.send(embed=embed)
                except Exception:
                    pass

            # DM if enabled
            if settings.get("levelup_dm_enabled", 0):
                try:
                    dm_msg = settings.get("levelup_dm_message") or f"You reached **Level {new_level}** in {message.guild.name}! Keep it up! 🚀"
                    dm_msg = dm_msg.replace("{level}", str(new_level)).replace("{server}", message.guild.name)
                    dm_embed = discord.Embed(
                        title="🎉 Level Up!",
                        description=dm_msg,
                        color=discord.Color(0x5865F2)
                    )
                    await message.author.send(embed=dm_embed)
                except Exception:
                    pass

            # Assign level rewards
            try:
                rewards = await self.bot.db.get_level_rewards(message.guild.id)
                for reward in rewards:
                    if reward["level"] == new_level:
                        role = message.guild.get_role(reward["role_id"])
                        if role and role not in message.author.roles:
                            try:
                                await message.author.add_roles(role, reason=f"XERO Level Reward: Level {new_level}")
                            except Exception as e:
                                logger.debug(f"Level reward role: {e}")
            except Exception as e:
                logger.debug(f"Level rewards: {e}")
        except Exception as e:
            logger.debug(f"Level up handler: {e}")

    # ══════════════════════════════════════════════════════════════════════
    # VOICE XP — on_voice_state_update
    # ══════════════════════════════════════════════════════════════════════

    # Track when users join voice: {guild_id: {user_id: join_time}}
    _voice_sessions: dict = {}

    @commands.Cog.listener()
    async def on_voice_state_update(
        self,
        member: discord.Member,
        before: discord.VoiceState,
        after: discord.VoiceState
    ):
        if member.bot:
            return

        guild_id = member.guild.id
        user_id  = member.id

        settings = await self.bot.db.get_guild_settings(guild_id)
        if not settings.get("voice_xp_enabled", 0):
            return

        # Init guild tracker
        if guild_id not in Events._voice_sessions:
            Events._voice_sessions[guild_id] = {}

        # Joined a voice channel
        if before.channel is None and after.channel is not None:
            # Don't count if muted/deafened alone
            real_members = [m for m in after.channel.members if not m.bot]
            if len(real_members) >= 1:
                Events._voice_sessions[guild_id][user_id] = datetime.datetime.utcnow()

        # Left a voice channel or switched to a channel with no others
        elif before.channel is not None:
            join_time = Events._voice_sessions.get(guild_id, {}).pop(user_id, None)
            if join_time:
                minutes = (datetime.datetime.utcnow() - join_time).total_seconds() / 60
                if minutes >= 1:
                    xp_rate = settings.get("voice_xp_rate", 5)
                    xp_gain = int(minutes * xp_rate)
                    xp_gain = max(1, min(xp_gain, 300))  # cap at 300 XP per session
                    try:
                        leveled_up, new_level = await self.bot.db.update_xp(user_id, guild_id, xp_gain)
                        logger.debug(f"Voice XP: {member} +{xp_gain}xp ({minutes:.1f}m) in {member.guild.name}")
                        if leveled_up:
                            await self._handle_level_up_voice(member, new_level, settings)
                    except Exception as e:
                        logger.debug(f"Voice XP update: {e}")

    async def _handle_level_up_voice(self, member: discord.Member, new_level: int, settings: dict):
        """Send level-up notification from voice XP."""
        try:
            ch_id = settings.get("level_up_channel_id")
            ch = member.guild.get_channel(ch_id) if ch_id else None
            if ch:
                embed = discord.Embed(
                    title="🎙️ Voice Level Up!",
                    description=(
                        f"{member.mention} earned enough voice XP to reach **Level {new_level}**! 🎤"
                    ),
                    color=discord.Color(0x5865F2),
                    timestamp=discord.utils.utcnow()
                )
                embed.set_thumbnail(url=member.display_avatar.url)
                embed.set_footer(text="XERO Voice XP")
                await ch.send(embed=embed)

            # Assign level rewards
            rewards = await self.bot.db.get_level_rewards(member.guild.id)
            for reward in rewards:
                if reward["level"] == new_level:
                    role = member.guild.get_role(reward["role_id"])
                    if role and role not in member.roles:
                        try:
                            await member.add_roles(role, reason=f"XERO Voice Level Reward: Level {new_level}")
                        except Exception:
                            pass
        except Exception as e:
            logger.debug(f"Voice level-up: {e}")


async def setup(bot):
    await bot.add_cog(Events(bot))
