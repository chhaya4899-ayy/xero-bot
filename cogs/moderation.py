"""XERO Bot — Moderation (16 commands)"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
import datetime
from utils.embeds import success_embed, error_embed, info_embed, warning_embed, mod_embed, comprehensive_embed

logger = logging.getLogger("XERO.Moderation")


def can_moderate(interaction: discord.Interaction, target: discord.Member) -> bool:
    if target.id == interaction.guild.owner_id:
        return False
    if interaction.user.id == interaction.guild.owner_id:
        return True
    return interaction.user.top_role > target.top_role


class Moderation(commands.GroupCog, name="mod"):
    def __init__(self, bot):
        self.bot = bot

    async def log_action(self, guild: discord.Guild, embed: discord.Embed):
        settings = await self.bot.db.get_guild_settings(guild.id)
        if settings.get("log_channel_id"):
            ch = guild.get_channel(settings["log_channel_id"])
            if ch:
                try:
                    await ch.send(embed=embed)
                except Exception:
                    pass

    # ── Warn ──────────────────────────────────────────────────────────────
    @app_commands.command(name="warn", description="Issue a formal warning to a user with reason logging.")
    @app_commands.describe(user="User to warn", reason="Reason for the warning")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def warn(self, interaction: discord.Interaction, user: discord.Member, reason: str = "No reason provided"):
        if not can_moderate(interaction, user):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You cannot moderate this user."), ephemeral=True)
        total = await self.bot.db.add_warning(interaction.guild.id, user.id, interaction.user.id, reason)
        case_id = await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "warn", reason)
        embed = mod_embed("warn", user, interaction.user, reason, case_id)
        embed.add_field(name="⚠️ Total Warnings", value=f"This user now has **{total}** warning(s).", inline=False)
        await interaction.response.send_message(embed=embed)
        await self.log_action(interaction.guild, embed)
        try:
            await user.send(embed=warning_embed(f"You were warned in {interaction.guild.name}", f"**Reason:** {reason}\n**Total Warnings:** {total}"))
        except Exception:
            pass

        # ── Auto-escalation via SmartMod ──────────────────────────────────
        smart_mod = self.bot.cogs.get("SmartMod")
        if smart_mod:
            await smart_mod.check_auto_escalation(interaction.guild, user, total, reason)

    # ── Warnings ──────────────────────────────────────────────────────────
    @app_commands.command(name="warnings", description="View all warnings for a user.")
    @app_commands.describe(user="User to check warnings for")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def warnings(self, interaction: discord.Interaction, user: discord.Member):
        warns = await self.bot.db.get_warnings(interaction.guild.id, user.id)
        if not warns:
            return await interaction.response.send_message(embed=info_embed("No Warnings", f"{user.mention} has no warnings."), ephemeral=True)
        embed = comprehensive_embed(
            title=f"⚠️ Warnings — {user.display_name}",
            description=f"**{len(warns)}** total warning(s)",
            color=discord.Color.orange(),
            thumbnail_url=user.display_avatar.url
        )
        for i, w in enumerate(warns[:10], 1):
            mod = interaction.guild.get_member(w["mod_id"])
            mod_name = mod.display_name if mod else f"ID:{w['mod_id']}"
            embed.add_field(name=f"Warning #{i}", value=f"**Reason:** {w['reason']}\n**By:** {mod_name}\n**When:** <t:{int(datetime.datetime.fromisoformat(w['timestamp']).timestamp())}:R>", inline=False)
        await interaction.response.send_message(embed=embed)

    # ── Clear Warnings ────────────────────────────────────────────────────
    @app_commands.command(name="clearwarns", description="Clear all warnings for a user.")
    @app_commands.describe(user="User to clear warnings for")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def clearwarns(self, interaction: discord.Interaction, user: discord.Member):
        await self.bot.db.clear_warnings(interaction.guild.id, user.id)
        await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "clearwarns", "All warnings cleared")
        await interaction.response.send_message(embed=success_embed("Warnings Cleared", f"All warnings for {user.mention} have been removed."))

    # ── Kick ──────────────────────────────────────────────────────────────
    @app_commands.command(name="kick", description="Kick a member from the server.")
    @app_commands.describe(user="Member to kick", reason="Reason for kick")
    @app_commands.checks.has_permissions(kick_members=True)
    async def kick(self, interaction: discord.Interaction, user: discord.Member, reason: str = "No reason provided"):
        if not can_moderate(interaction, user):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You cannot kick this user."), ephemeral=True)
        try:
            await user.send(embed=error_embed(f"Kicked from {interaction.guild.name}", f"**Reason:** {reason}"))
        except Exception:
            pass
        await user.kick(reason=f"{reason} | By: {interaction.user}")
        case_id = await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "kick", reason)
        embed = mod_embed("kick", user, interaction.user, reason, case_id)
        await interaction.response.send_message(embed=embed)
        await self.log_action(interaction.guild, embed)

    # ── Ban ───────────────────────────────────────────────────────────────
    @app_commands.command(name="ban", description="Ban a member from the server.")
    @app_commands.describe(user="Member to ban", reason="Reason for ban", delete_days="Days of messages to delete (0-7)")
    @app_commands.checks.has_permissions(ban_members=True)
    async def ban(self, interaction: discord.Interaction, user: discord.Member, reason: str = "No reason provided", delete_days: int = 0):
        if not can_moderate(interaction, user):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You cannot ban this user."), ephemeral=True)
        delete_days = max(0, min(7, delete_days))
        try:
            await user.send(embed=error_embed(f"Banned from {interaction.guild.name}", f"**Reason:** {reason}"))
        except Exception:
            pass
        await user.ban(reason=f"{reason} | By: {interaction.user}", delete_message_days=delete_days)
        case_id = await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "ban", reason)
        embed = mod_embed("ban", user, interaction.user, reason, case_id)
        await interaction.response.send_message(embed=embed)
        await self.log_action(interaction.guild, embed)

    # ── Unban ─────────────────────────────────────────────────────────────
    @app_commands.command(name="unban", description="Unban a user by their ID.")
    @app_commands.describe(user_id="User ID to unban", reason="Reason for unban")
    @app_commands.checks.has_permissions(ban_members=True)
    async def unban(self, interaction: discord.Interaction, user_id: str, reason: str = "No reason provided"):
        try:
            uid = int(user_id)
            banned = [entry async for entry in interaction.guild.bans()]
            user = next((b.user for b in banned if b.user.id == uid), None)
            if not user:
                return await interaction.response.send_message(embed=error_embed("Not Found", "That user is not banned."), ephemeral=True)
            await interaction.guild.unban(user, reason=f"{reason} | By: {interaction.user}")
            case_id = await self.bot.db.add_mod_case(interaction.guild.id, uid, interaction.user.id, "unban", reason)
            embed = success_embed("User Unbanned", f"**{user}** has been unbanned.\n**Reason:** {reason}\n**Case:** #{case_id}")
            await interaction.response.send_message(embed=embed)
        except ValueError:
            await interaction.response.send_message(embed=error_embed("Invalid ID", "Please provide a valid user ID."), ephemeral=True)

    # ── Softban ───────────────────────────────────────────────────────────
    @app_commands.command(name="softban", description="Ban then immediately unban to delete messages.")
    @app_commands.describe(user="Member to softban", reason="Reason for softban")
    @app_commands.checks.has_permissions(ban_members=True)
    async def softban(self, interaction: discord.Interaction, user: discord.Member, reason: str = "No reason provided"):
        if not can_moderate(interaction, user):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You cannot softban this user."), ephemeral=True)
        await user.ban(reason=f"Softban: {reason}", delete_message_days=7)
        await interaction.guild.unban(user, reason="Softban — immediate unban")
        case_id = await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "softban", reason)
        embed = mod_embed("softban", user, interaction.user, reason, case_id)
        embed.description = "User softbanned (banned+unbanned to purge messages, still in server)"
        await interaction.response.send_message(embed=embed)
        await self.log_action(interaction.guild, embed)

    # ── Timeout ───────────────────────────────────────────────────────────
    @app_commands.command(name="timeout", description="Timeout (mute) a member for a specified duration.")
    @app_commands.describe(user="Member to timeout", minutes="Timeout duration in minutes (max 40320)", reason="Reason")
    @app_commands.checks.has_permissions(moderate_members=True)
    async def timeout(self, interaction: discord.Interaction, user: discord.Member, minutes: int, reason: str = "No reason provided"):
        if not can_moderate(interaction, user):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You cannot timeout this user."), ephemeral=True)
        minutes = max(1, min(40320, minutes))
        until = discord.utils.utcnow() + datetime.timedelta(minutes=minutes)
        await user.timeout(until, reason=f"{reason} | By: {interaction.user}")
        case_id = await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "timeout", reason, minutes)
        embed = mod_embed("timeout", user, interaction.user, reason, case_id, f"{minutes} minutes")
        await interaction.response.send_message(embed=embed)
        await self.log_action(interaction.guild, embed)
        try:
            await user.send(embed=warning_embed(f"Timed out in {interaction.guild.name}", f"**Duration:** {minutes} minutes\n**Reason:** {reason}"))
        except Exception:
            pass

    # ── Untimeout ─────────────────────────────────────────────────────────
    @app_commands.command(name="untimeout", description="Remove timeout from a member.")
    @app_commands.describe(user="Member to remove timeout from", reason="Reason")
    @app_commands.checks.has_permissions(moderate_members=True)
    async def untimeout(self, interaction: discord.Interaction, user: discord.Member, reason: str = "No reason provided"):
        await user.timeout(None, reason=f"{reason} | By: {interaction.user}")
        case_id = await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "untimeout", reason)
        await interaction.response.send_message(embed=success_embed("Timeout Removed", f"{user.mention}'s timeout has been removed.\n**Reason:** {reason}\n**Case:** #{case_id}"))

    # ── Purge ─────────────────────────────────────────────────────────────
    @app_commands.command(name="purge", description="Delete multiple messages at once (up to 100).")
    @app_commands.describe(amount="Number of messages to delete", user="Only delete messages from this user (optional)")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def purge(self, interaction: discord.Interaction, amount: int, user: discord.Member = None):
        amount = max(1, min(100, amount))
        await interaction.response.defer(ephemeral=True)
        check = (lambda m: m.author == user) if user else None
        deleted = await interaction.channel.purge(limit=amount, check=check)
        target_info = f" from {user.mention}" if user else ""
        await interaction.followup.send(embed=success_embed("Messages Purged", f"Deleted **{len(deleted)}** messages{target_info}."), ephemeral=True)
        log_embed = success_embed("Purge", f"**{len(deleted)}** messages deleted in {interaction.channel.mention}{target_info} by {interaction.user.mention}")
        await self.log_action(interaction.guild, log_embed)

    # ── Slowmode ──────────────────────────────────────────────────────────
    @app_commands.command(name="slowmode", description="Set channel slowmode delay.")
    @app_commands.describe(seconds="Slowmode in seconds (0 to disable, max 21600)", channel="Channel to set slowmode in")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def slowmode(self, interaction: discord.Interaction, seconds: int, channel: discord.TextChannel = None):
        ch = channel or interaction.channel
        seconds = max(0, min(21600, seconds))
        await ch.edit(slowmode_delay=seconds)
        if seconds == 0:
            await interaction.response.send_message(embed=success_embed("Slowmode Disabled", f"Slowmode removed from {ch.mention}."))
        else:
            await interaction.response.send_message(embed=success_embed("Slowmode Set", f"Slowmode in {ch.mention} set to **{seconds}s**."))

    # ── Lock ──────────────────────────────────────────────────────────────
    @app_commands.command(name="lock", description="Lock a channel so only staff can send messages.")
    @app_commands.describe(channel="Channel to lock", reason="Reason for lock")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def lock(self, interaction: discord.Interaction, channel: discord.TextChannel = None, reason: str = "No reason provided"):
        ch = channel or interaction.channel
        overwrite = ch.overwrites_for(interaction.guild.default_role)
        overwrite.send_messages = False
        await ch.set_permissions(interaction.guild.default_role, overwrite=overwrite)
        await interaction.response.send_message(embed=success_embed("Channel Locked", f"🔒 {ch.mention} has been locked.\n**Reason:** {reason}"))
        await ch.send(embed=warning_embed("Channel Locked", f"This channel has been locked by {interaction.user.mention}.\n**Reason:** {reason}"))

    # ── Unlock ────────────────────────────────────────────────────────────
    @app_commands.command(name="unlock", description="Unlock a previously locked channel.")
    @app_commands.describe(channel="Channel to unlock")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def unlock(self, interaction: discord.Interaction, channel: discord.TextChannel = None):
        ch = channel or interaction.channel
        overwrite = ch.overwrites_for(interaction.guild.default_role)
        overwrite.send_messages = None
        await ch.set_permissions(interaction.guild.default_role, overwrite=overwrite)
        await interaction.response.send_message(embed=success_embed("Channel Unlocked", f"🔓 {ch.mention} has been unlocked."))
        await ch.send(embed=success_embed("Channel Unlocked", f"This channel has been unlocked by {interaction.user.mention}."))

    # ── Nickname ──────────────────────────────────────────────────────────
    @app_commands.command(name="nick", description="Change a member's nickname.")
    @app_commands.describe(user="Member to rename", nickname="New nickname (leave empty to reset)")
    @app_commands.checks.has_permissions(manage_nicknames=True)
    async def nick(self, interaction: discord.Interaction, user: discord.Member, nickname: str = None):
        if not can_moderate(interaction, user):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You cannot modify this user's nickname."), ephemeral=True)
        old_nick = user.display_name
        await user.edit(nick=nickname)
        if nickname:
            await interaction.response.send_message(embed=success_embed("Nickname Changed", f"{user.mention}: **{old_nick}** → **{nickname}**"))
        else:
            await interaction.response.send_message(embed=success_embed("Nickname Reset", f"{user.mention}'s nickname has been reset to **{user.name}**."))

    # ── History ───────────────────────────────────────────────────────────
    @app_commands.command(name="history", description="View moderation history for a user.")
    @app_commands.describe(user="User to check history for")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def history(self, interaction: discord.Interaction, user: discord.Member):
        cases = await self.bot.db.get_mod_cases(interaction.guild.id, user.id, limit=15)
        warns = await self.bot.db.get_warnings(interaction.guild.id, user.id)
        embed = comprehensive_embed(
            title=f"📋 Mod History — {user.display_name}",
            description=f"**{len(cases)}** case(s) | **{len(warns)}** warning(s)",
            color=discord.Color.orange(),
            thumbnail_url=user.display_avatar.url
        )
        if cases:
            for c in cases[:8]:
                mod = interaction.guild.get_member(c["mod_id"])
                mod_name = mod.display_name if mod else f"ID:{c['mod_id']}"
                ts = int(datetime.datetime.fromisoformat(c["timestamp"]).timestamp())
                embed.add_field(name=f"Case #{c['case_id']} — {c['action'].upper()}", value=f"**Reason:** {c['reason']}\n**By:** {mod_name} | <t:{ts}:R>", inline=False)
        else:
            embed.description = "No moderation history found for this user."
        await interaction.response.send_message(embed=embed)


    @app_commands.command(name="tempban", description="Ban a user for a set duration. Auto-unbanned when time expires.")
    @app_commands.describe(user="User to ban", duration="Duration (e.g. 1h, 6h, 1d, 7d)", reason="Reason for the ban")
    @app_commands.checks.has_permissions(ban_members=True)
    async def tempban(self, interaction: discord.Interaction, user: discord.Member, duration: str, reason: str = "Temporary ban"):
        import re as _re
        if not can_moderate(interaction, user):
            return await interaction.response.send_message(embed=error_embed("Permission Denied","You cannot moderate this user."), ephemeral=True)
        # Parse duration
        match = _re.match(r"(\d+)([hHdDmM])", duration.strip())
        if not match:
            return await interaction.response.send_message(embed=error_embed("Invalid Duration","Use format like `1h`, `6h`, `1d`, `7d`."), ephemeral=True)
        amount, unit = int(match.group(1)), match.group(2).lower()
        seconds = amount * {"h":3600,"d":86400,"m":60}[unit]
        if seconds > 86400*30:
            return await interaction.response.send_message(embed=error_embed("Too Long","Max temp-ban is 30 days. Use /mod ban for permanent."), ephemeral=True)
        expires_at = datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(seconds=seconds)
        unit_name  = {"h":"hour","d":"day","m":"minute"}[unit]
        # DM user before ban
        try:
            await user.send(embed=warning_embed(
                f"Temporarily Banned from {interaction.guild.name}",
                f"**Reason:** {reason}\n**Duration:** {amount} {unit_name}(s)\n**Expires:** <t:{int(expires_at.timestamp())}:F>"
            ))
        except Exception: pass
        await user.ban(reason=f"XERO TempBan ({duration}): {reason}", delete_message_days=0)
        case_id = await self.bot.db.add_mod_case(interaction.guild.id, user.id, interaction.user.id, "tempban", f"{reason} [expires <t:{int(expires_at.timestamp())}:R>]", duration=duration)
        # Store for auto-unban
        async with self.bot.db._db_context() as db:
            await db.execute("CREATE TABLE IF NOT EXISTS temp_bans (case_id INTEGER PRIMARY KEY, guild_id INTEGER, user_id INTEGER, expires_at TEXT, reason TEXT)")
            await db.execute("INSERT OR REPLACE INTO temp_bans VALUES (?,?,?,?,?)", (case_id, interaction.guild.id, user.id, expires_at.isoformat(), reason))
            await db.commit()
        embed = mod_embed("tempban", user, interaction.user, reason, case_id)
        embed.add_field(name="⏰ Duration",  value=f"{amount} {unit_name}(s)", inline=True)
        embed.add_field(name="⏰ Expires",   value=f"<t:{int(expires_at.timestamp())}:R>", inline=True)
        await interaction.response.send_message(embed=embed)
        await self.log_action(interaction.guild, embed)

    @app_commands.command(name="note", description="Add a private mod note on a user. Only mods can see these.")
    @app_commands.describe(user="User to add note for", note="The note content")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def note(self, interaction: discord.Interaction, user: discord.Member, note: str):
        async with self.bot.db._db_context() as db:
            await db.execute("CREATE TABLE IF NOT EXISTS mod_notes (id INTEGER PRIMARY KEY AUTOINCREMENT, guild_id INTEGER, user_id INTEGER, mod_id INTEGER, content TEXT, created_at TEXT DEFAULT (datetime(\'now\')))")
            await db.execute("INSERT INTO mod_notes (guild_id, user_id, mod_id, content) VALUES (?,?,?,?)",
                             (interaction.guild.id, user.id, interaction.user.id, note))
            await db.commit()
        embed = success_embed("📝 Note Added", f"Private note added for {user.mention}:\n> {note}\n\nUse `/mod notes {user.display_name}` to view all notes.")
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="notes", description="View all private mod notes on a user.")
    @app_commands.describe(user="User to view notes for")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def notes(self, interaction: discord.Interaction, user: discord.Member):
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT * FROM mod_notes WHERE guild_id=? AND user_id=? ORDER BY id DESC LIMIT 10",
                                  (interaction.guild.id, user.id)) as c:
                rows = [dict(r) for r in await c.fetchall()]
        if not rows:
            return await interaction.response.send_message(embed=info_embed("No Notes", f"No mod notes for {user.mention}."), ephemeral=True)
        embed = comprehensive_embed(title=f"📝 Mod Notes — {user.display_name}", color=discord.Color.orange(), thumbnail_url=user.display_avatar.url)
        for r in rows:
            mod = interaction.guild.get_member(r["mod_id"])
            mod_name = mod.display_name if mod else f"ID:{r['mod_id']}"
            embed.add_field(name=f"Note #{r['id']} by {mod_name}", value=f"> {r['content']}\n*{r['created_at'][:10]}*", inline=False)
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="case-edit", description="Edit the reason on an existing mod case.")
    @app_commands.describe(case_id="Case ID to edit", reason="New reason")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def case_edit(self, interaction: discord.Interaction, case_id: int, reason: str):
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT * FROM mod_cases WHERE case_id=? AND guild_id=?", (case_id, interaction.guild.id)) as c:
                row = await c.fetchone()
            if not row:
                return await interaction.response.send_message(embed=error_embed("Not Found", f"Case #{case_id} not found."), ephemeral=True)
            await db.execute("UPDATE mod_cases SET reason=? WHERE case_id=?", (reason, case_id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Case Updated", f"Case **#{case_id}** reason updated to:\n> {reason}"), ephemeral=True)

    @app_commands.command(name="massban", description="Ban multiple users by ID at once. For post-raid cleanup.")
    @app_commands.describe(user_ids="Space-separated list of user IDs to ban", reason="Reason for mass ban")
    @app_commands.checks.has_permissions(ban_members=True)
    async def massban(self, interaction: discord.Interaction, user_ids: str, reason: str = "Mass ban"):
        await interaction.response.defer()
        ids     = [i.strip() for i in user_ids.split() if i.strip().isdigit()]
        if not ids:
            return await interaction.followup.send(embed=error_embed("No IDs","Provide space-separated numeric user IDs."))
        banned  = []; failed = []
        for uid in ids[:50]:  # Cap at 50
            try:
                await interaction.guild.ban(discord.Object(int(uid)), reason=f"XERO MassBan: {reason}", delete_message_days=1)
                banned.append(uid)
                await self.bot.db.add_mod_case(interaction.guild.id, int(uid), interaction.user.id, "ban", f"Mass ban: {reason}")
            except Exception: failed.append(uid)
        embed = success_embed("🔨 Mass Ban Complete",
            f"✅ Banned **{len(banned)}** user(s)\n"
            + (f"❌ Failed: **{len(failed)}** (`{'`, `'.join(failed[:5])}`)" if failed else ""))
        embed.set_footer(text=f"Reason: {reason}  •  By: {interaction.user}")
        await interaction.followup.send(embed=embed)
        await self.log_action(interaction.guild, embed)

async def setup(bot):
    await bot.add_cog(Moderation(bot))
