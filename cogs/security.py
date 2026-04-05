"""
XERO Bot — Security System v2
Better than WickBot. Free. AI-enhanced.
Anti-nuke, permission watchdog, webhook protection, bot protection,
alt-account scoring, smart lockdown, raid mode, security dashboard.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, datetime, asyncio, aiosqlite, re, math
from utils.embeds import (
    success_embed, error_embed, info_embed, warning_embed,
    comprehensive_embed, XERO, FOOTER_MOD
)

logger = logging.getLogger("XERO.Security")

# ── In-memory state ───────────────────────────────────────────────────────────
# Anti-nuke: guild_id -> {user_id -> {action -> [timestamps]}}
NUKE_TRACK: dict = {}
# Smart lockdown channel permission snapshots: guild_id -> {channel_id -> overwrites}
LOCKDOWN_SNAPSHOTS: dict = {}


class Security(commands.GroupCog, name="security"):
    def __init__(self, bot):
        self.bot = bot

    # ══════════════════════════════════════════════════════════════════════
    # INTERNAL ANTI-NUKE ENGINE (called from events.py listeners)
    # ══════════════════════════════════════════════════════════════════════

    async def track_nuke_action(self, guild: discord.Guild,
                                user: discord.Member, action: str):
        """
        Track rapid destructive actions. Trigger response at threshold.
        Call from events.py on_guild_channel_delete, on_guild_role_delete, etc.
        """
        try:
            settings = await self.bot.db.get_guild_settings(guild.id)
            if not settings.get("anti_nuke_enabled", 0):
                return

            gid, uid = guild.id, user.id
            now = datetime.datetime.now()

            if gid not in NUKE_TRACK: NUKE_TRACK[gid] = {}
            if uid not in NUKE_TRACK[gid]: NUKE_TRACK[gid][uid] = {}
            if action not in NUKE_TRACK[gid][uid]: NUKE_TRACK[gid][uid][action] = []

            NUKE_TRACK[gid][uid][action].append(now)
            cutoff = now - datetime.timedelta(seconds=10)
            NUKE_TRACK[gid][uid][action] = [
                t for t in NUKE_TRACK[gid][uid][action] if t > cutoff
            ]
            count     = len(NUKE_TRACK[gid][uid][action])
            threshold = settings.get("anti_nuke_threshold", 3)

            if count >= threshold:
                NUKE_TRACK[gid][uid][action] = []
                await self._trigger_anti_nuke(guild, user, action, count, settings)
                # Log to DB
                try:
                    async with self.bot.db._db_context() as db:
                        await db.execute(
                            "INSERT INTO antinuke_log (guild_id, user_id, action, count) "
                            "VALUES (?,?,?,?)",
                            (guild.id, user.id, action, count)
                        )
                        await db.commit()
                except Exception:
                    pass
        except Exception as e:
            logger.error(f"track_nuke_action: {e}")

    async def _trigger_anti_nuke(self, guild, user, action, count, settings):
        """Strip all dangerous roles, alert admins, log."""
        logger.warning(f"🚨 ANTI-NUKE: {user} in {guild.name} — {count}x {action}")
        try:
            if user.id != guild.owner_id:
                safe_roles = [
                    r for r in user.roles
                    if not r.managed and r != guild.default_role
                ]
                if safe_roles:
                    await user.remove_roles(
                        *safe_roles,
                        reason=f"XERO Anti-Nuke: {count}x {action} in 10s"
                    )
        except Exception as e:
            logger.error(f"Anti-nuke role removal: {e}")

        embed = discord.Embed(
            title="🚨  ANTI-NUKE TRIGGERED",
            description=(
                f"**{user.mention}** (`{user.id}`) performed "
                f"**{count}x `{action}`** within 10 seconds.\n\n"
                f"**Action taken:** All administrative roles removed.\n"
                f"Verify this person and use `/security restore-roles` if it was a mistake."
            ),
            color=discord.Color.red(),
            timestamp=discord.utils.utcnow()
        )
        embed.set_thumbnail(url=user.display_avatar.url)
        embed.set_footer(text="XERO Anti-Nuke  •  Automatic Protection")

        log_ch = guild.get_channel(settings.get("log_channel_id") or 0)
        if log_ch:
            try:
                await log_ch.send(content="@here", embed=embed)
            except Exception:
                pass

        for m in guild.members:
            if m.guild_permissions.administrator and not m.bot and m.id != user.id:
                try:
                    await m.send(embed=embed)
                except Exception:
                    pass

    # ══════════════════════════════════════════════════════════════════════
    # ALT ACCOUNT SCORING (called from events.py on_member_join)
    # ══════════════════════════════════════════════════════════════════════

    async def check_alt_score(self, member: discord.Member):
        """Calculate suspicion score. Auto-quarantine if >= 75."""
        try:
            score    = 0
            factors  = []
            now      = discord.utils.utcnow()
            age_days = (now - member.created_at).days

            if age_days < 7:
                score += 30; factors.append(f"+30  Account under 7 days old ({age_days}d)")
            elif age_days < 30:
                score += 20; factors.append(f"+20  Account under 30 days old ({age_days}d)")

            if member.display_avatar.key == member.default_avatar.key:
                score += 15; factors.append("+15  Default avatar")

            # Random-looking username (all numbers or very short or long random)
            name = member.name
            if re.fullmatch(r'\d+', name):
                score += 10; factors.append("+10  Username is all numbers")
            elif re.fullmatch(r'[a-z0-9]{16,}', name.lower()):
                score += 10; factors.append("+10  Username looks randomly generated")

            # Rejoins
            try:
                async with self.bot.db._db_context() as db:
                    async with db.execute(
                        "SELECT COUNT(*) FROM member_join_history WHERE user_id=? AND guild_id=?",
                        (member.id, member.guild.id)
                    ) as c:
                        rejoins = (await c.fetchone())[0]
                if rejoins >= 3:
                    score += 25; factors.append(f"+25  Rejoined {rejoins} times before")
            except Exception:
                pass

            # Record this join
            try:
                async with self.bot.db._db_context() as db:
                    await db.execute(
                        "INSERT INTO member_join_history (user_id, guild_id) VALUES (?,?)",
                        (member.id, member.guild.id)
                    )
                    await db.commit()
            except Exception:
                pass

            if score < 30:
                return  # Not suspicious

            settings = await self.bot.db.get_guild_settings(member.guild.id)
            log_ch   = member.guild.get_channel(settings.get("log_channel_id") or 0)

            if score >= 50 and log_ch:
                embed = discord.Embed(
                    title="🔍  Alt Account Alert",
                    description=(
                        f"{member.mention} (`{member.id}`) joined with a "
                        f"**suspicion score of {score}/100**"
                    ),
                    color=discord.Color.orange(),
                    timestamp=discord.utils.utcnow()
                )
                embed.add_field(name="Score Breakdown", value="\n".join(factors), inline=False)
                embed.add_field(name="Account Age", value=f"{age_days} days", inline=True)
                embed.add_field(name="Action",
                                value="Auto-quarantined" if score >= 75 else "Alert only",
                                inline=True)
                embed.set_thumbnail(url=member.display_avatar.url)
                embed.set_footer(text="XERO Alt Detection  •  /security alt-score to check manually")
                try:
                    await log_ch.send(embed=embed)
                except Exception:
                    pass

            # Auto-quarantine at 75+
            if score >= 75:
                q_role_id = settings.get("quarantine_role_id")
                if q_role_id:
                    q_role = member.guild.get_role(q_role_id)
                    if q_role:
                        try:
                            await member.add_roles(
                                q_role,
                                reason=f"XERO Alt Detection: suspicion score {score}"
                            )
                        except Exception:
                            pass

        except Exception as e:
            logger.error(f"check_alt_score: {e}")

    # ══════════════════════════════════════════════════════════════════════
    # SLASH COMMANDS
    # ══════════════════════════════════════════════════════════════════════

    @app_commands.command(name="setup",
                          description="Security dashboard — view all settings + recent actions.")
    @app_commands.checks.has_permissions(administrator=True)
    async def setup(self, interaction: discord.Interaction):
        await interaction.response.defer()
        s = await self.bot.db.get_guild_settings(interaction.guild.id)

        def tog(v, on="✅ On", off="❌ Off"): return on if v else off

        embed = comprehensive_embed(
            title=f"🔒  Security Dashboard — {interaction.guild.name}",
            color=XERO.PRIMARY
        )
        embed.add_field(name="🚨 Anti-Nuke", value=(
            f"{tog(s.get('anti_nuke_enabled',0))}\n"
            f"Threshold: **{s.get('anti_nuke_threshold',3)}** actions/10s"
        ), inline=True)
        embed.add_field(name="👶 Account Age", value=(
            f"Min: **{s.get('min_account_age_days',0)}d**\n"
            f"Action: `{s.get('account_age_action','kick_dm')}`"
        ), inline=True)
        embed.add_field(name="🔗 Link Filter", value=(
            f"{tog(s.get('link_filter_enabled',0))}"
        ), inline=True)
        embed.add_field(name="💾 Role Restore",  value=tog(s.get("role_restore_enabled",0)), inline=True)
        embed.add_field(name="🪝 Webhook Prot.", value=tog(s.get("webhook_protection_enabled",1)), inline=True)
        embed.add_field(name="🤖 Bot Prot.",     value=tog(s.get("bot_protection_enabled",0)), inline=True)
        embed.add_field(name="🔐 Perm Watchdog", value=tog(s.get("perm_watchdog_enabled",1)), inline=True)

        # Raid mode
        raid_on     = s.get("raid_mode_enabled", 0)
        raid_until  = s.get("raid_mode_until")
        raid_status = "✅ ACTIVE" if raid_on else "❌ Off"
        if raid_on and raid_until:
            raid_status += f"\nExpires: <t:{int(datetime.datetime.fromisoformat(str(raid_until)).timestamp())}:R>"
        embed.add_field(name="⚡ Raid Mode", value=raid_status, inline=True)

        # Quarantine count
        q_count = 0
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT COUNT(*) FROM aegis_quarantine WHERE guild_id=? AND status='pending'",
                    (interaction.guild.id,)
                ) as c:
                    q_count = (await c.fetchone())[0]
        except Exception:
            pass
        embed.add_field(name="🔒 Quarantined", value=str(q_count), inline=True)

        # Last 5 anti-nuke triggers
        recent = []
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT user_id, action, count, triggered_at FROM antinuke_log "
                    "WHERE guild_id=? ORDER BY triggered_at DESC LIMIT 5",
                    (interaction.guild.id,)
                ) as c:
                    recent = await c.fetchall()
        except Exception:
            pass

        if recent:
            lines = []
            for uid, act, cnt, ts in recent:
                lines.append(f"<@{uid}>  **{cnt}x {act}**  `{str(ts)[:16]}`")
            embed.add_field(name="🕓 Recent Anti-Nuke Triggers",
                            value="\n".join(lines), inline=False)

        embed.add_field(name="Commands", value=(
            "`/security anti-nuke` · `/security account-age` · `/security link-filter`\n"
            "`/security role-restore` · `/security raid-mode` · `/security alt-score`\n"
            "`/security webhook-protection` · `/security bot-protection`\n"
            "`/security lockdown` · `/security unlock` · `/security restore-roles`"
        ), inline=False)
        embed.set_footer(text="XERO Security  •  Beating WickBot — free")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="anti-nuke",
                          description="Toggle anti-nuke protection.")
    @app_commands.describe(enabled="Enable/disable", threshold="Actions in 10s to trigger (2–10)")
    @app_commands.checks.has_permissions(administrator=True)
    async def anti_nuke(self, interaction: discord.Interaction,
                        enabled: bool, threshold: int = 3):
        threshold = max(2, min(10, threshold))
        await self.bot.db.update_guild_setting(interaction.guild.id, "anti_nuke_enabled",   1 if enabled else 0)
        await self.bot.db.update_guild_setting(interaction.guild.id, "anti_nuke_threshold", threshold)
        embed = success_embed(
            f"Anti-Nuke {'Enabled' if enabled else 'Disabled'}",
            f"**Status:** {'✅ Active' if enabled else '❌ Inactive'}\n"
            f"**Trigger:** {threshold} destructive actions within 10 seconds\n"
            f"**Watches:** channel delete, role delete, mass ban, webhook create, "
            f"permission escalation, bulk message delete, emoji delete\n"
            f"**Response:** All admin roles stripped instantly + DM all admins"
        )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="account-age",
                          description="Block accounts younger than X days from joining.")
    @app_commands.describe(days="Minimum age in days (0 = disabled)",
                           action="Action for underage accounts")
    @app_commands.choices(action=[
        app_commands.Choice(name="Kick silently",    value="kick"),
        app_commands.Choice(name="Kick + DM reason", value="kick_dm"),
        app_commands.Choice(name="Ban",              value="ban"),
    ])
    @app_commands.checks.has_permissions(administrator=True)
    async def account_age(self, interaction: discord.Interaction,
                          days: int, action: str = "kick_dm"):
        days = max(0, min(365, days))
        await self.bot.db.update_guild_setting(interaction.guild.id, "min_account_age_days", days)
        await self.bot.db.update_guild_setting(interaction.guild.id, "account_age_action",  action)
        msg = (f"Accounts under **{days} days** will be **{action.replace('_',' ')}** on join.\n"
               f"*Most raid bots use accounts <7 days old. Setting 7+ blocks ~90% of raids.*"
               if days > 0 else "Account age filter **disabled**.")
        await interaction.response.send_message(embed=success_embed("Account Age Filter", msg))

    @app_commands.command(name="link-filter",
                          description="Block external links. Manage allowed domains.")
    @app_commands.describe(enabled="Enable/disable", add_domain="Allow this domain",
                           remove_domain="Remove this domain")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def link_filter(self, interaction: discord.Interaction,
                          enabled: bool = None,
                          add_domain: str = None,
                          remove_domain: str = None):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "CREATE TABLE IF NOT EXISTS allowed_domains "
                "(guild_id INTEGER, domain TEXT, PRIMARY KEY(guild_id, domain))"
            )
            if enabled is not None:
                await self.bot.db.update_guild_setting(
                    interaction.guild.id, "link_filter_enabled", 1 if enabled else 0
                )
            if add_domain:
                d = add_domain.lower().strip().replace("https://","").replace("http://","").split("/")[0]
                await db.execute(
                    "INSERT OR IGNORE INTO allowed_domains VALUES (?,?)",
                    (interaction.guild.id, d)
                )
            if remove_domain:
                d = remove_domain.lower().strip().replace("https://","").replace("http://","").split("/")[0]
                await db.execute(
                    "DELETE FROM allowed_domains WHERE guild_id=? AND domain=?",
                    (interaction.guild.id, d)
                )
            await db.commit()
            async with db.execute(
                "SELECT domain FROM allowed_domains WHERE guild_id=? ORDER BY domain",
                (interaction.guild.id,)
            ) as c:
                domains = [r[0] for r in await c.fetchall()]

        s      = await self.bot.db.get_guild_settings(interaction.guild.id)
        status = "✅ Active" if s.get("link_filter_enabled") else "❌ Inactive"
        dlist  = "\n".join(f"• `{d}`" for d in domains) if domains else "*None — all links blocked when enabled*"
        await interaction.response.send_message(embed=success_embed(
            "Link Filter", f"**Status:** {status}\n\n**Allowed Domains:**\n{dlist}\n\n"
            "*discord.com, tenor.com, giphy.com always allowed.*"
        ))

    @app_commands.command(name="role-restore",
                          description="Automatically restore roles when a member rejoins.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def role_restore(self, interaction: discord.Interaction, enabled: bool):
        await self.bot.db.update_guild_setting(
            interaction.guild.id, "role_restore_enabled", 1 if enabled else 0
        )
        msg = (
            "Roles are saved when members leave and restored on rejoin.\n"
            "Managed/integration roles are excluded."
            if enabled else "Role restore disabled."
        )
        await interaction.response.send_message(embed=success_embed("Role Restore", msg))

    @app_commands.command(name="webhook-protection",
                          description="Auto-delete webhooks created by non-admins.")
    @app_commands.checks.has_permissions(administrator=True)
    async def webhook_protection(self, interaction: discord.Interaction, enabled: bool):
        await self.bot.db.update_guild_setting(
            interaction.guild.id, "webhook_protection_enabled", 1 if enabled else 0
        )
        msg = (
            "**Webhook Protection ON**\n"
            "Any webhook created by a non-admin will be instantly deleted and the "
            "attempt logged. Stops phishing attacks dead."
            if enabled else "Webhook protection disabled."
        )
        await interaction.response.send_message(embed=success_embed("Webhook Protection", msg))

    @app_commands.command(name="bot-protection",
                          description="Block bots added without Manage Server permission.")
    @app_commands.checks.has_permissions(administrator=True)
    async def security_bot_protection(self, interaction: discord.Interaction, enabled: bool):
        await self.bot.db.update_guild_setting(
            interaction.guild.id, "bot_protection_enabled", 1 if enabled else 0
        )
        msg = (
            "**Bot Protection ON**\n"
            "If a bot is added by someone without **Manage Server** permission, "
            "it will be kicked immediately and all admins alerted."
            if enabled else "Bot protection disabled."
        )
        await interaction.response.send_message(embed=success_embed("Bot Protection", msg))

    @app_commands.command(name="raid-mode",
                          description="Pre-emptively lock server against raids.")
    @app_commands.describe(
        enabled="Enable or disable raid mode",
        duration_minutes="Auto-disable after this many minutes (0 = manual)",
        min_age_days="Kick any joining account younger than this (default 7)"
    )
    @app_commands.checks.has_permissions(administrator=True)
    async def raid_mode(self, interaction: discord.Interaction,
                        enabled: bool,
                        duration_minutes: int = 30,
                        min_age_days: int = 7):
        await interaction.response.defer()
        guild = interaction.guild

        if enabled:
            # Set @everyone view_channel=False in all text channels
            locked_count = 0
            for ch in guild.text_channels:
                try:
                    overwrite = ch.overwrites_for(guild.default_role)
                    overwrite.send_messages = False
                    await ch.set_permissions(
                        guild.default_role, overwrite=overwrite,
                        reason="XERO Raid Mode activated"
                    )
                    locked_count += 1
                except Exception:
                    pass

            expires = None
            if duration_minutes > 0:
                expires = (datetime.datetime.now() +
                           datetime.timedelta(minutes=duration_minutes)).isoformat()

            await self.bot.db.update_guild_setting(guild.id, "raid_mode_enabled",      1)
            await self.bot.db.update_guild_setting(guild.id, "raid_mode_until",        expires)
            await self.bot.db.update_guild_setting(guild.id, "raid_mode_min_age_days", min_age_days)

            expire_txt = (f"Auto-disables in **{duration_minutes}m**"
                          if duration_minutes > 0 else "Manual disable required")
            embed = discord.Embed(
                title="⚡  RAID MODE ACTIVE",
                description=(
                    f"**{locked_count}** channels locked.\n"
                    f"Accounts under **{min_age_days} days** old will be kicked on join.\n"
                    f"{expire_txt}\n\n"
                    f"Run `/security raid-mode enabled:False` to disable."
                ),
                color=discord.Color.red(),
                timestamp=discord.utils.utcnow()
            )
            await interaction.followup.send(embed=embed)

            # Schedule auto-disable
            if duration_minutes > 0:
                async def _auto_disable():
                    await asyncio.sleep(duration_minutes * 60)
                    try:
                        s = await self.bot.db.get_guild_settings(guild.id)
                        if s.get("raid_mode_enabled"):
                            await self._disable_raid_mode(guild)
                    except Exception:
                        pass
                asyncio.create_task(_auto_disable())
        else:
            await self._disable_raid_mode(guild)
            await interaction.followup.send(embed=success_embed(
                "Raid Mode Disabled",
                "Server channels have been unlocked and raid mode is off."
            ))

    async def _disable_raid_mode(self, guild: discord.Guild):
        """Unlock all channels and clear raid mode settings."""
        try:
            for ch in guild.text_channels:
                try:
                    overwrite = ch.overwrites_for(guild.default_role)
                    if overwrite.send_messages is False:
                        overwrite.send_messages = None
                        await ch.set_permissions(
                            guild.default_role, overwrite=overwrite,
                            reason="XERO Raid Mode deactivated"
                        )
                except Exception:
                    pass
            await self.bot.db.update_guild_setting(guild.id, "raid_mode_enabled", 0)
            await self.bot.db.update_guild_setting(guild.id, "raid_mode_until",   None)
        except Exception as e:
            logger.error(f"_disable_raid_mode: {e}")

    @app_commands.command(name="lockdown",
                          description="Lock all channels — stores exact permission snapshot for restore.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def lockdown(self, interaction: discord.Interaction):
        await interaction.response.defer()
        guild  = interaction.guild
        locked = 0
        LOCKDOWN_SNAPSHOTS[guild.id] = {}

        for ch in guild.text_channels:
            try:
                # Snapshot existing overwrites for @everyone
                existing = ch.overwrites_for(guild.default_role)
                LOCKDOWN_SNAPSHOTS[guild.id][ch.id] = existing
                # Lock
                lock_ow = discord.PermissionOverwrite(**{k: v for k, v in existing})
                lock_ow.send_messages = False
                await ch.set_permissions(
                    guild.default_role, overwrite=lock_ow,
                    reason="XERO Lockdown"
                )
                locked += 1
            except Exception:
                pass

        embed = discord.Embed(
            title="🔒  Server Locked Down",
            description=(
                f"**{locked}** channels locked.\n"
                f"Permission snapshots saved — `/security unlock` will restore exact previous state.\n\n"
                f"*Use only in emergencies. Inform your team.*"
            ),
            color=discord.Color.red(),
            timestamp=discord.utils.utcnow()
        )
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="unlock",
                          description="Unlock all channels and restore exact previous permissions.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def unlock(self, interaction: discord.Interaction):
        await interaction.response.defer()
        guild    = interaction.guild
        restored = 0
        snapshot = LOCKDOWN_SNAPSHOTS.get(guild.id, {})

        for ch in guild.text_channels:
            try:
                if ch.id in snapshot:
                    # Restore exact pre-lockdown permissions
                    await ch.set_permissions(
                        guild.default_role, overwrite=snapshot[ch.id],
                        reason="XERO Unlock: restoring pre-lockdown permissions"
                    )
                else:
                    # No snapshot — just re-enable send_messages
                    ow = ch.overwrites_for(guild.default_role)
                    ow.send_messages = None
                    await ch.set_permissions(
                        guild.default_role, overwrite=ow,
                        reason="XERO Unlock"
                    )
                restored += 1
            except Exception:
                pass

        if guild.id in LOCKDOWN_SNAPSHOTS:
            del LOCKDOWN_SNAPSHOTS[guild.id]

        await interaction.followup.send(embed=success_embed(
            "Server Unlocked",
            f"**{restored}** channels restored to their pre-lockdown permission state."
        ))

    @app_commands.command(name="alt-score",
                          description="Check the alt/suspicion score for a user.")
    @app_commands.describe(user="User to check")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def alt_score(self, interaction: discord.Interaction, user: discord.Member):
        await interaction.response.defer(ephemeral=True)
        now      = discord.utils.utcnow()
        age_days = (now - user.created_at).days

        score   = 0
        factors = []

        if age_days < 7:
            score += 30; factors.append(f"+30  Account under 7 days ({age_days}d)")
        elif age_days < 30:
            score += 20; factors.append(f"+20  Account under 30 days ({age_days}d)")

        if user.display_avatar.key == user.default_avatar.key:
            score += 15; factors.append("+15  Default avatar")

        name = user.name
        if re.fullmatch(r'\d+', name):
            score += 10; factors.append("+10  Username is all numbers")
        elif re.fullmatch(r'[a-z0-9]{16,}', name.lower()):
            score += 10; factors.append("+10  Username looks randomly generated")

        rejoins = 0
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT COUNT(*) FROM member_join_history WHERE user_id=? AND guild_id=?",
                    (user.id, interaction.guild.id)
                ) as c:
                    rejoins = (await c.fetchone())[0]
        except Exception:
            pass

        if rejoins >= 3:
            score += 25; factors.append(f"+25  Rejoined {rejoins} times")

        risk_label = (
            "🟢 Low"    if score < 30 else
            "🟡 Medium" if score < 50 else
            "🟠 High"   if score < 75 else
            "🔴 Very High — auto-quarantine threshold"
        )

        embed = discord.Embed(
            title=f"🔍  Alt Score — {user.display_name}",
            color=discord.Color.red() if score >= 75 else
                  discord.Color.orange() if score >= 50 else
                  discord.Color.green(),
            timestamp=discord.utils.utcnow()
        )
        embed.add_field(name="Score",       value=f"**{score} / 100**", inline=True)
        embed.add_field(name="Risk Level",  value=risk_label, inline=True)
        embed.add_field(name="Account Age", value=f"{age_days} days", inline=True)
        if factors:
            embed.add_field(name="Score Breakdown", value="\n".join(factors), inline=False)
        else:
            embed.add_field(name="Score Breakdown", value="No risk factors detected.", inline=False)
        embed.set_thumbnail(url=user.display_avatar.url)
        await interaction.followup.send(embed=embed, ephemeral=True)

    @app_commands.command(name="restore-roles",
                          description="Manually restore saved roles for a member.")
    @app_commands.describe(user="Member to restore roles for")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def restore_roles_cmd(self, interaction: discord.Interaction, user: discord.Member):
        await interaction.response.defer(ephemeral=True)
        async with self.bot.db._db_context() as db:
            async with db.execute(
                "SELECT role_ids FROM member_roles WHERE user_id=? AND guild_id=?",
                (user.id, interaction.guild.id)
            ) as c:
                row = await c.fetchone()

        if not row or not row[0]:
            return await interaction.followup.send(
                embed=error_embed("No Saved Roles", f"No roles saved for {user.mention}."),
                ephemeral=True
            )

        role_ids = [int(r) for r in row[0].split(",") if r.strip()]
        restored, failed = [], []
        for rid in role_ids:
            role = interaction.guild.get_role(rid)
            if role and role not in user.roles and not role.managed:
                try:
                    await user.add_roles(role, reason=f"XERO Role Restore by {interaction.user}")
                    restored.append(role.mention)
                except Exception:
                    failed.append(role.name)

        embed = success_embed(
            "Roles Restored",
            f"**{user.mention}** — restored **{len(restored)}** role(s)\n"
            + (", ".join(restored) if restored else "None restored")
            + (f"\n⚠️ Failed: {', '.join(failed)}" if failed else "")
        )
        await interaction.followup.send(embed=embed, ephemeral=True)

    @app_commands.command(name="view",
                          description="View all current security settings.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def view(self, interaction: discord.Interaction):
        # Redirect to setup (which is now the full dashboard)
        await self.setup.callback(self, interaction)


async def setup(bot):
    await bot.add_cog(Security(bot))
