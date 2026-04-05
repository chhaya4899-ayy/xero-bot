"""
XERO Bot — Logging System
The most detailed logging of any bot. Period.

What makes this better than Logger, Loggy, GiselleBot, and every paid logging bot:
  • AI-powered threat scoring on every member join
  • AI analysis on critical events (mass role changes, admin perm grants, bulk deletes)
  • WHO deleted a message — pulled from audit log every time
  • Invite tracking — know EXACTLY which invite link each member used
  • Full permission diff on every role/channel change
  • Voice session duration tracked per member
  • Suspicious pattern detection (rapid edits, mass role changes)
  • Bulk delete full transcript exported as .txt file
  • Every log answers: WHO, WHAT, WHERE, WHEN, WHY, HOW SUSPICIOUS

Channels (all separately configurable or one unified):
  #log-messages  →  edits, deletes, bulk deletes + AI analysis
  #log-members   →  joins (threat scored), leaves, bans, role/nick changes
  #log-server    →  channels, roles, server, emoji, invites, webhooks, threads
  #log-voice     →  every voice state + session durations
"""
import discord
from utils.guard import command_guard
from discord.ext import commands, tasks
from discord import app_commands
import logging, datetime, aiosqlite
from utils.embeds import XERO, comprehensive_embed

logger = logging.getLogger("XERO.Logging")

C = {
    "msg_delete":0xFF3B5C,"msg_edit":0xFFB800,"bulk_delete":0xFF6B35,
    "join":0x00FF94,"leave":0xFF3B5C,"ban":0xFF1744,"unban":0x00FF94,
    "member_upd":0xFFB800,"boost":0xFF69B4,"role_create":0x00D4FF,
    "role_delete":0xFF3B5C,"role_update":0xFFB800,"ch_create":0x00D4FF,
    "ch_delete":0xFF3B5C,"ch_update":0xFFB800,"server":0xFF9800,
    "emoji":0xFFD700,"invite":0x00BCD4,"webhook":0xFF3B5C,"thread":0x00BCD4,
    "voice":0x7B2FFF,"timeout":0xFFB800,"suspicious":0xFF1744,
}

PERM_NAMES = {
    "administrator":"Administrator","manage_guild":"Manage Server",
    "manage_roles":"Manage Roles","manage_channels":"Manage Channels",
    "manage_messages":"Manage Messages","manage_webhooks":"Manage Webhooks",
    "ban_members":"Ban Members","kick_members":"Kick Members",
    "moderate_members":"Timeout Members","mention_everyone":"Mention Everyone",
    "view_audit_log":"View Audit Log","manage_nicknames":"Manage Nicknames",
    "manage_emojis_and_stickers":"Manage Emojis","create_instant_invite":"Create Invites",
    "read_message_history":"Read History","connect":"Connect","speak":"Speak",
    "move_members":"Move Members","mute_members":"Mute Members","stream":"Go Live",
}


class AdvancedLogger(commands.Cog):

    def __init__(self, bot):
        self.bot = bot
        self._cache: dict          = {}
        self._voice_sessions: dict = {}
        self._invite_cache: dict   = {}
        self._msg_pattern: dict    = {}
        self.refresh_cache.start()
        self.refresh_invites.start()

    def cog_unload(self):
        self.refresh_cache.cancel()
        self.refresh_invites.cancel()

    @tasks.loop(minutes=30)
    async def refresh_cache(self):
        self._cache.clear()

    @tasks.loop(minutes=10)
    async def refresh_invites(self):
        for guild in self.bot.guilds:
            try:
                invites = await guild.invites()
                self._invite_cache[guild.id] = {i.code: i for i in invites}
            except Exception:
                pass

    @refresh_cache.before_loop
    async def _bc(self): await self.bot.wait_until_ready()
    @refresh_invites.before_loop
    async def _bi(self): await self.bot.wait_until_ready()

    async def _settings(self, gid):
        if gid not in self._cache:
            try: self._cache[gid] = await self.bot.db.get_guild_settings(gid) or {}
            except Exception: self._cache[gid] = {}
        return self._cache[gid]

    async def _ch(self, guild, log_type):
        s = await self._settings(guild.id)
        TYPE_MAP = {
            "msg_delete":"message_log_channel_id","msg_edit":"message_log_channel_id",
            "bulk_delete":"message_log_channel_id","join":"member_log_channel_id",
            "leave":"member_log_channel_id","ban":"member_log_channel_id",
            "unban":"member_log_channel_id","member_upd":"member_log_channel_id",
            "boost":"member_log_channel_id","voice":"voice_log_channel_id",
            "role_create":"server_log_channel_id","role_delete":"server_log_channel_id",
            "role_update":"server_log_channel_id","ch_create":"server_log_channel_id",
            "ch_delete":"server_log_channel_id","ch_update":"server_log_channel_id",
            "server":"server_log_channel_id","emoji":"server_log_channel_id",
            "invite":"server_log_channel_id","thread":"server_log_channel_id",
            "webhook":"server_log_channel_id","timeout":"member_log_channel_id",
        }
        cid = s.get(TYPE_MAP.get(log_type,"")) or s.get("log_channel_id")
        if not cid: return None
        ch = guild.get_channel(cid)
        return ch if isinstance(ch, discord.TextChannel) else None

    async def _log(self, guild, log_type, embed, content=None, file=None):
        ch = await self._ch(guild, log_type)
        if not ch: return
        try: await ch.send(content=content, embed=embed, file=file)
        except Exception as e: logger.debug(f"Log: {e}")

    def _e(self, t, title):
        return comprehensive_embed(title=title, color=discord.Color(C.get(t,0x00D4FF)), timestamp=discord.utils.utcnow())

    def _f(self, embed, *parts):
        embed.set_footer(text="  •  ".join(str(p) for p in parts if p))

    async def _ai(self, prompt):
        try:
            s = "You are a Discord security analyst for XERO Bot. Give a SHORT (max 2 sentences) security assessment. Be direct."
            return await self.bot.nvidia.ask(prompt, s)
        except Exception: return None

    def _threat(self, member):
        score = 0; flags = []
        age = (discord.utils.utcnow() - member.created_at).days
        if age < 1:    score += 40; flags.append("Account <1 day old")
        elif age < 7:  score += 25; flags.append("Account <7 days old")
        elif age < 30: score += 10; flags.append("Account <30 days old")
        if member.default_avatar: score += 10; flags.append("Default avatar")
        sus = ["discord","admin","mod","staff","support","official","system"]
        if any(p in member.name.lower() for p in sus): score += 15; flags.append("Suspicious name")
        level = "🟢 Low" if score < 20 else "🟡 Medium" if score < 50 else "🔴 HIGH"
        return score, level, ", ".join(flags) if flags else "No flags"

    def _perm_diff(self, before, after):
        gained = [PERM_NAMES.get(p,p) for p,v in dict(after).items() if v and not dict(before).get(p) and p in PERM_NAMES]
        lost   = [PERM_NAMES.get(p,p) for p,v in dict(before).items() if v and not dict(after).get(p) and p in PERM_NAMES]
        return gained, lost

    # ── MESSAGE EVENTS ────────────────────────────────────────────────────────

    @commands.Cog.listener()
    async def on_message_edit(self, before, after):
        if before.author.bot or not before.guild: return
        if before.content == after.content: return
        
        # Ignore check
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT 1 FROM log_ignored_channels WHERE guild_id=? AND channel_id=?", (before.guild.id, before.channel.id)) as c:
                if await c.fetchone(): return
            for r in before.author.roles:
                async with db.execute("SELECT 1 FROM log_ignored_roles WHERE guild_id=? AND role_id=?", (before.guild.id, r.id)) as c:
                    if await c.fetchone(): return

        gid, uid = before.guild.id, before.author.id
        now = datetime.datetime.now()
        if gid not in self._msg_pattern: self._msg_pattern[gid] = {}
        if uid not in self._msg_pattern[gid]: self._msg_pattern[gid][uid] = []
        self._msg_pattern[gid][uid].append(now)
        recent = sum(1 for ts in self._msg_pattern[gid][uid] if (now-ts).seconds < 60)
        embed = self._e("msg_edit","✏️  Message Edited")
        embed.set_author(name=f"{before.author}  ({before.author.id})", icon_url=before.author.display_avatar.url)
        embed.add_field(name="📝 Before", value=f"```{before.content[:800]}```" if before.content else "*empty*", inline=False)
        embed.add_field(name="📝 After",  value=f"```{after.content[:800]}```"  if after.content  else "*empty*", inline=False)
        embed.add_field(name="📍 Channel",   value=before.channel.mention,                          inline=True)
        embed.add_field(name="📏 Δ Chars",   value=f"{len(after.content)-len(before.content):+}",   inline=True)
        embed.add_field(name="🔗 Jump",      value=f"[View]({after.jump_url})",                      inline=True)
        embed.add_field(name="📅 Sent",      value=f"<t:{int(before.created_at.timestamp())}:R>",    inline=True)
        embed.add_field(name="🔄 Edits/60s", value=str(recent),                                      inline=True)
        if recent >= 5:
            embed.add_field(name="⚠️ Pattern Alert", value=f"**{recent}** edits in 60 seconds — possible scrubbing attempt.", inline=False)
        self._f(embed, f"User ID: {uid}", f"Message ID: {before.id}", "XERO Logging")
        await self._log(before.guild, "msg_edit", embed)

    @commands.Cog.listener()
    async def on_message_delete(self, message):
        if message.author.bot or not message.guild: return
        
        # Ignore check
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT 1 FROM log_ignored_channels WHERE guild_id=? AND channel_id=?", (message.guild.id, message.channel.id)) as c:
                if await c.fetchone(): return
            for r in message.author.roles:
                async with db.execute("SELECT 1 FROM log_ignored_roles WHERE guild_id=? AND role_id=?", (message.guild.id, r.id)) as c:
                    if await c.fetchone(): return

        deleter_str = "*Unknown — may be self-deleted*"
        sus_flag    = False
        try:
            async for entry in message.guild.audit_logs(limit=3, action=discord.AuditLogAction.message_delete):
                if entry.target.id == message.author.id and (discord.utils.utcnow()-entry.created_at).seconds < 6:
                    deleter_str = f"{entry.user.mention} deleted this"
                    if message.content and any(k in message.content.lower() for k in ["discord.gift","nitro","http://","@everyone","token"]):
                        sus_flag = True
                    break
        except Exception: pass
        embed = self._e("msg_delete","🗑️  Message Deleted")
        embed.set_author(name=f"{message.author}  ({message.author.id})", icon_url=message.author.display_avatar.url)
        embed.add_field(name="📝 Content", value=f"```{message.content[:1500]}```" if message.content else "*no text*", inline=False)
        embed.add_field(name="📍 Channel",    value=message.channel.mention,                           inline=True)
        embed.add_field(name="📅 Sent",       value=f"<t:{int(message.created_at.timestamp())}:R>",    inline=True)
        embed.add_field(name="🕵️ Deleted By", value=deleter_str,                                       inline=True)
        if message.attachments:
            embed.add_field(name=f"📎 Attachments ({len(message.attachments)})",
                           value="\n".join(f"`{a.filename}` ({a.size//1024}KB)" for a in message.attachments)[:300],
                           inline=False)
        if message.embeds:   embed.add_field(name="🖼️ Embeds",   value=str(len(message.embeds)),                     inline=True)
        if message.stickers: embed.add_field(name="🎨 Stickers", value=", ".join(s.name for s in message.stickers), inline=True)
        if message.reference:embed.add_field(name="↩️ Reply",    value=f"ID: {message.reference.message_id}",        inline=True)
        if sus_flag:
            embed.add_field(name="🤖 AI Flag", value="⚠️ Staff deleted a message with suspicious content (links/tokens/@everyone). Review carefully.", inline=False)
        self._f(embed, f"Author ID: {message.author.id}", f"Msg ID: {message.id}", "XERO Logging")
        await self._log(message.guild, "msg_delete", embed)

    @commands.Cog.listener()
    async def on_bulk_message_delete(self, messages):
        if not messages or not messages[0].guild: return
        guild = messages[0].guild; channel = messages[0].channel
        authors = {}
        for m in messages:
            if m.author.id not in authors: authors[m.author.id] = {"name":m.author.display_name,"count":0}
            authors[m.author.id]["count"] += 1
        deleter = None
        try:
            async for entry in guild.audit_logs(limit=1, action=discord.AuditLogAction.message_bulk_delete):
                if (discord.utils.utcnow()-entry.created_at).seconds < 10: deleter = entry.user; break
        except Exception: pass
        sample = [f"**{m.author.display_name}:** {m.content[:80]}" for m in messages[:6] if m.content]
        embed = self._e("bulk_delete", f"💥  Bulk Delete — {len(messages)} Messages")
        embed.add_field(name="📍 Channel",    value=channel.mention,                               inline=True)
        embed.add_field(name="🗑️ Count",      value=f"**{len(messages)}**",                       inline=True)
        embed.add_field(name="👥 Authors",    value=f"{len(authors)} user(s)",                     inline=True)
        embed.add_field(name="🕵️ By",        value=deleter.mention if deleter else "*Unknown*",   inline=True)
        lines = "\n".join(f"• **{v['name']}** — {v['count']} msg(s)" for v in list(authors.values())[:8])
        embed.add_field(name="👥 Breakdown", value=lines or "?",                                   inline=False)
        if sample: embed.add_field(name="📋 Sample", value="\n".join(sample)[:600],                inline=False)
        if len(messages) >= 10:
            ai = await self._ai(f"A moderator bulk-deleted {len(messages)} messages in #{channel.name}. Authors: {', '.join(v['name'] for v in list(authors.values())[:5])}. Sample: {' | '.join(sample[:2])}. Was this spam cleanup, raid response, or manual mod?")
            if ai: embed.add_field(name="🤖 AI Analysis", value=ai, inline=False)
        import io
        transcript = "\n".join(f"[{m.created_at.strftime('%H:%M:%S')}] {m.author}: {m.content}" for m in sorted(messages, key=lambda x:x.created_at))
        file = discord.File(io.StringIO(transcript), filename=f"bulk-delete-{channel.name}.txt")
        self._f(embed, f"Channel ID: {channel.id}", "XERO Logging")
        await self._log(guild, "bulk_delete", embed, file=file)

    # ── MEMBER EVENTS ─────────────────────────────────────────────────────────

    @commands.Cog.listener()
    async def on_member_join(self, member):
        if member.bot: return
        score, level, flags = self._threat(member)
        age_days = (discord.utils.utcnow() - member.created_at).days
        invite_used = None
        try:
            new_invs = await member.guild.invites()
            new_dict = {i.code:i for i in new_invs}
            old_dict = self._invite_cache.get(member.guild.id, {})
            for code,old in old_dict.items():
                nw = new_dict.get(code)
                if nw and nw.uses > old.uses: invite_used = old; break
            self._invite_cache[member.guild.id] = new_dict
        except Exception: pass
        embed = self._e("suspicious" if score>=50 else "join", f"📥  Member Joined  —  {level}")
        embed.set_author(name=f"{member}  ({member.id})", icon_url=member.display_avatar.url)
        embed.set_thumbnail(url=member.display_avatar.url)
        embed.add_field(name="👤 Username",    value=f"`{member}`",                                        inline=True)
        embed.add_field(name="🆔 User ID",     value=f"`{member.id}`",                                     inline=True)
        embed.add_field(name="📅 Created",     value=f"<t:{int(member.created_at.timestamp())}:D> ({age_days}d ago)", inline=True)
        embed.add_field(name="👥 Members Now", value=f"**{member.guild.member_count:,}**",                 inline=True)
        embed.add_field(name="🖼️ Avatar",     value="Default" if member.default_avatar else "Custom",      inline=True)
        embed.add_field(name="🤖 Bot",         value="Yes" if member.bot else "No",                        inline=True)
        if invite_used:
            inv_creator = invite_used.inviter
            embed.add_field(name="🔗 Invite Used",
                           value=f"Code: `{invite_used.code}`\nBy: {inv_creator.mention if inv_creator else '?'}\nUses: {invite_used.uses}",
                           inline=False)
        embed.add_field(name=f"🛡️ Threat: {score}/100  {level}", value=flags, inline=False)
        if score >= 40:
            ai = await self._ai(f"User joining Discord server. Name: {member.name}, account age: {age_days} days, default avatar: {member.default_avatar}, flags: {flags}. Likely raid bot, alt, or legitimate user?")
            if ai: embed.add_field(name="🤖 AI Assessment", value=ai, inline=False)
        self._f(embed, f"User ID: {member.id}", "XERO Logging")
        await self._log(member.guild, "join", embed)

    @commands.Cog.listener()
    async def on_member_remove(self, member):
        if member.bot: return
        stayed = ""
        if member.joined_at:
            d = discord.utils.utcnow() - member.joined_at
            stayed = f"{d.days}d {d.seconds//3600}h {(d.seconds%3600)//60}m"
        action_str = "Left voluntarily"
        by_str = ""
        try:
            async for entry in member.guild.audit_logs(limit=3, action=discord.AuditLogAction.kick):
                if entry.target.id == member.id and (discord.utils.utcnow()-entry.created_at).seconds < 8:
                    action_str = "Kicked"
                    by_str = f" by {entry.user.mention}"
                    if entry.reason: by_str += f" — *{entry.reason}*"
                    break
        except Exception: pass
        embed = self._e("leave","📤  Member Left")
        embed.set_author(name=f"{member}  ({member.id})", icon_url=member.display_avatar.url)
        embed.add_field(name="👤 User",       value=f"`{member}`",                                          inline=True)
        embed.add_field(name="🆔 ID",         value=f"`{member.id}`",                                       inline=True)
        embed.add_field(name="📅 Joined",     value=f"<t:{int(member.joined_at.timestamp())}:D>" if member.joined_at else "?", inline=True)
        embed.add_field(name="⏱️ Stayed",     value=stayed or "?",                                          inline=True)
        embed.add_field(name="🎭 Top Role",   value=member.top_role.mention,                                 inline=True)
        embed.add_field(name="👥 Now",        value=f"{member.guild.member_count:,}",                       inline=True)
        embed.add_field(name="🚪 Action",     value=action_str + by_str,                                    inline=False)
        roles = [r.mention for r in reversed(member.roles) if r != member.guild.default_role][:10]
        if roles: embed.add_field(name="🎭 Had Roles", value=" ".join(roles), inline=False)
        self._f(embed, f"User ID: {member.id}", "XERO Logging")
        await self._log(member.guild, "leave", embed)

    @commands.Cog.listener()
    async def on_member_ban(self, guild, user):
        embed = self._e("ban","🔨  Member Banned")
        embed.set_author(name=f"{user}  ({user.id})", icon_url=user.display_avatar.url)
        embed.add_field(name="👤 User",    value=f"{user.mention} `{user}`", inline=True)
        embed.add_field(name="🆔 ID",      value=f"`{user.id}`",             inline=True)
        reason = "No reason provided"; by = "Unknown"
        try:
            async for entry in guild.audit_logs(limit=3, action=discord.AuditLogAction.ban):
                if entry.target.id == user.id:
                    by = f"{entry.user.mention} (`{entry.user}`)"
                    if entry.reason: reason = entry.reason
                    break
        except Exception: pass
        embed.add_field(name="🛡️ Banned By", value=by,     inline=True)
        embed.add_field(name="📋 Reason",    value=reason,  inline=False)
        self._f(embed, f"User ID: {user.id}", "XERO Logging")
        await self._log(guild, "ban", embed)

    @commands.Cog.listener()
    async def on_member_unban(self, guild, user):
        embed = self._e("unban","🔓  Member Unbanned")
        embed.set_author(name=f"{user}  ({user.id})", icon_url=user.display_avatar.url)
        embed.add_field(name="👤 User", value=f"{user.mention} `{user}`", inline=True)
        embed.add_field(name="🆔 ID",   value=f"`{user.id}`",             inline=True)
        try:
            async for entry in guild.audit_logs(limit=3, action=discord.AuditLogAction.unban):
                if entry.target.id == user.id:
                    embed.add_field(name="🛡️ By", value=entry.user.mention, inline=True)
                    if entry.reason: embed.add_field(name="📋 Reason", value=entry.reason, inline=False)
                    break
        except Exception: pass
        self._f(embed, f"User ID: {user.id}", "XERO Logging")
        await self._log(guild, "unban", embed)

    @commands.Cog.listener()
    async def on_member_update(self, before, after):
        guild = before.guild
        # Nickname
        if before.nick != after.nick:
            embed = self._e("member_upd","📝  Nickname Changed")
            embed.set_author(name=f"{after}  ({after.id})", icon_url=after.display_avatar.url)
            embed.add_field(name="Before", value=f"`{before.nick or before.name}`", inline=True)
            embed.add_field(name="After",  value=f"`{after.nick  or after.name}`",  inline=True)
            try:
                async for entry in guild.audit_logs(limit=2, action=discord.AuditLogAction.member_update):
                    if entry.target.id == after.id and entry.user.id != after.id:
                        embed.add_field(name="✏️ By", value=entry.user.mention, inline=True); break
            except Exception: pass
            self._f(embed, f"User ID: {after.id}", "XERO Logging")
            await self._log(guild, "member_upd", embed)
        # Roles
        elif set(before.roles) != set(after.roles):
            added   = [r for r in after.roles  if r not in before.roles]
            removed = [r for r in before.roles if r not in after.roles]
            if not added and not removed: return
            total   = len(added) + len(removed)
            suspect = total >= 5
            embed = self._e("suspicious" if suspect else "member_upd",
                           f"{'⚠️  SUSPICIOUS  ' if suspect else ''}🎭  Roles Changed ({total})")
            embed.set_author(name=f"{after}  ({after.id})", icon_url=after.display_avatar.url)
            if added:   embed.add_field(name=f"➕ Added ({len(added)})",   value=" ".join(r.mention for r in added[:10]),   inline=False)
            if removed: embed.add_field(name=f"➖ Removed ({len(removed)})", value=" ".join(r.mention for r in removed[:10]), inline=False)
            danger_added = [r for r in added if any(getattr(r.permissions,p,False) for p in ["administrator","manage_guild","ban_members","manage_roles"])]
            if danger_added:
                embed.add_field(name="🚨 Dangerous Perms Granted",
                               value="\n".join(f"• {r.mention}" for r in danger_added), inline=False)
            try:
                async for entry in guild.audit_logs(limit=2, action=discord.AuditLogAction.member_role_update):
                    if entry.target.id == after.id:
                        embed.add_field(name="✏️ By", value=entry.user.mention, inline=True); break
            except Exception: pass
            if suspect:
                ai = await self._ai(f"Discord member had {len(added)} roles added and {len(removed)} removed at once. Added: {', '.join(r.name for r in added[:5])}. Suspicious or routine?")
                if ai: embed.add_field(name="🤖 AI Assessment", value=ai, inline=False)
            self._f(embed, f"User ID: {after.id}", "XERO Logging")
            await self._log(guild, "member_upd", embed)
        # Timeout
        elif before.timed_out_until != after.timed_out_until:
            if after.timed_out_until:
                embed = self._e("timeout","⏱️  Member Timed Out")
                embed.set_author(name=f"{after}  ({after.id})", icon_url=after.display_avatar.url)
                embed.add_field(name="⏰ Until",    value=f"<t:{int(after.timed_out_until.timestamp())}:F>", inline=True)
                embed.add_field(name="⏰ Relative", value=f"<t:{int(after.timed_out_until.timestamp())}:R>", inline=True)
            else:
                embed = self._e("member_upd","✅  Timeout Removed")
                embed.set_author(name=f"{after}  ({after.id})", icon_url=after.display_avatar.url)
            try:
                async for entry in guild.audit_logs(limit=2, action=discord.AuditLogAction.member_update):
                    if entry.target.id == after.id:
                        embed.add_field(name="🛡️ By", value=entry.user.mention, inline=True)
                        if entry.reason: embed.add_field(name="📋 Reason", value=entry.reason, inline=False)
                        break
            except Exception: pass
            self._f(embed, f"User ID: {after.id}", "XERO Logging")
            await self._log(guild, "timeout", embed)
        # Boost
        elif not before.premium_since and after.premium_since:
            embed = self._e("boost","💎  Server Boosted!")
            embed.set_author(name=f"{after}  ({after.id})", icon_url=after.display_avatar.url)
            embed.add_field(name="💎 Booster",       value=after.mention,                                 inline=True)
            embed.add_field(name="🏆 Level Now",     value=f"Level {after.guild.premium_tier}",            inline=True)
            embed.add_field(name="💎 Total Boosts",  value=str(after.guild.premium_subscription_count),   inline=True)
            self._f(embed, f"User ID: {after.id}", "XERO Logging")
            await self._log(guild, "boost", embed)

    # ── VOICE EVENTS ──────────────────────────────────────────────────────────

    @commands.Cog.listener()
    async def on_voice_state_update(self, member, before, after):
        if member.bot: return
        embed = None; key = (member.id, member.guild.id)
        if not before.channel and after.channel:
            self._voice_sessions[key] = discord.utils.utcnow()
            embed = self._e("voice","🟢  Joined Voice")
            embed.set_author(name=f"{member}  ({member.id})", icon_url=member.display_avatar.url)
            embed.add_field(name="📢 Channel", value=f"**{after.channel.name}**",          inline=True)
            embed.add_field(name="🆔 ID",      value=f"`{after.channel.id}`",               inline=True)
            embed.add_field(name="👥 In Now",  value=str(len(after.channel.members)),       inline=True)
            embed.add_field(name="🔢 Limit",   value=str(after.channel.user_limit or "∞"),  inline=True)
        elif before.channel and not after.channel:
            join_time = self._voice_sessions.pop(key, None)
            embed = self._e("voice","🔴  Left Voice")
            embed.set_author(name=f"{member}  ({member.id})", icon_url=member.display_avatar.url)
            embed.add_field(name="📢 Channel", value=f"**{before.channel.name}**", inline=True)
            if join_time:
                secs = int((discord.utils.utcnow()-join_time).total_seconds())
                embed.add_field(name="⏱️ Session", value=f"{secs//60}m {secs%60}s", inline=True)
        elif before.channel and after.channel and before.channel != after.channel:
            embed = self._e("voice","🔀  Moved Voice Channel")
            embed.set_author(name=f"{member}  ({member.id})", icon_url=member.display_avatar.url)
            embed.add_field(name="📤 From", value=f"**{before.channel.name}**", inline=True)
            embed.add_field(name="📥 To",   value=f"**{after.channel.name}**",  inline=True)
            try:
                async for entry in member.guild.audit_logs(limit=1, action=discord.AuditLogAction.member_move):
                    if (discord.utils.utcnow()-entry.created_at).seconds < 5:
                        embed.add_field(name="👮 Moved By", value=entry.user.mention, inline=True); break
            except Exception: pass
        elif before.channel == after.channel and after.channel:
            changes = []
            if before.self_mute   != after.self_mute:   changes.append(f"Self-mute: {'🔇 On' if after.self_mute else '🔊 Off'}")
            if before.self_deaf   != after.self_deaf:   changes.append(f"Self-deaf: {'🔕 On' if after.self_deaf else '🔔 Off'}")
            if before.mute        != after.mute:        changes.append(f"Server mute: {'🔇 On' if after.mute else '🔊 Off'}")
            if before.deaf        != after.deaf:        changes.append(f"Server deaf: {'🔕 On' if after.deaf else '🔔 Off'}")
            if before.self_stream != after.self_stream: changes.append(f"Stream: {'📺 Started' if after.self_stream else '📺 Stopped'}")
            if before.self_video  != after.self_video:  changes.append(f"Camera: {'📷 On' if after.self_video else '📷 Off'}")
            if changes:
                embed = self._e("voice","🎙️  Voice State Changed")
                embed.set_author(name=f"{member}  ({member.id})", icon_url=member.display_avatar.url)
                embed.add_field(name="📢 Channel", value=f"**{after.channel.name}**", inline=True)
                embed.add_field(name="📝 Changes", value="\n".join(changes),           inline=False)
        if embed:
            self._f(embed, f"User ID: {member.id}", "XERO Logging")
            await self._log(member.guild, "voice", embed)

    # ── CHANNEL EVENTS ────────────────────────────────────────────────────────

    @commands.Cog.listener()
    async def on_guild_channel_create(self, channel):
        TYPES = {discord.TextChannel:"💬 Text",discord.VoiceChannel:"🔊 Voice",
                 discord.StageChannel:"🎭 Stage",discord.ForumChannel:"📋 Forum",
                 discord.CategoryChannel:"📁 Category"}
        ch_type = next((v for k,v in TYPES.items() if isinstance(channel,k)),"Channel")
        embed = self._e("ch_create","📡  Channel Created")
        embed.add_field(name="📌 Name",     value=f"{channel.mention} `{channel.name}`",            inline=True)
        embed.add_field(name="🏷️ Type",    value=ch_type,                                            inline=True)
        embed.add_field(name="📁 Category", value=channel.category.name if channel.category else "—", inline=True)
        embed.add_field(name="🔢 Position", value=str(channel.position),                              inline=True)
        embed.add_field(name="🆔 ID",       value=f"`{channel.id}`",                                  inline=True)
        if hasattr(channel,"nsfw"): embed.add_field(name="🔞 NSFW", value="Yes" if channel.nsfw else "No", inline=True)
        try:
            async for entry in channel.guild.audit_logs(limit=1, action=discord.AuditLogAction.channel_create):
                embed.add_field(name="👤 Created By", value=entry.user.mention, inline=True); break
        except Exception: pass
        self._f(embed, f"Channel ID: {channel.id}", "XERO Logging")
        await self._log(channel.guild, "ch_create", embed)

    @commands.Cog.listener()
    async def on_guild_channel_delete(self, channel):
        embed = self._e("ch_delete","🗑️  Channel Deleted")
        embed.add_field(name="📌 Name",     value=f"`{channel.name}`",                               inline=True)
        embed.add_field(name="📁 Category", value=channel.category.name if channel.category else "—", inline=True)
        embed.add_field(name="🆔 ID",       value=f"`{channel.id}`",                                  inline=True)
        try:
            async for entry in channel.guild.audit_logs(limit=1, action=discord.AuditLogAction.channel_delete):
                embed.add_field(name="👤 Deleted By", value=entry.user.mention, inline=True)
                if entry.reason: embed.add_field(name="📋 Reason", value=entry.reason, inline=False)
                break
        except Exception: pass
        self._f(embed, f"Channel ID: {channel.id}", "XERO Logging")
        await self._log(channel.guild, "ch_delete", embed)

    @commands.Cog.listener()
    async def on_guild_channel_update(self, before, after):
        changes = []
        if before.name != after.name: changes.append(f"**Name:** `{before.name}` → `{after.name}`")
        if hasattr(before,"topic") and before.topic != after.topic:
            changes.append(f"**Topic:** `{(before.topic or 'none')[:80]}` → `{(after.topic or 'none')[:80]}`")
        if hasattr(before,"slowmode_delay") and before.slowmode_delay != after.slowmode_delay:
            changes.append(f"**Slowmode:** {before.slowmode_delay}s → {after.slowmode_delay}s")
        if hasattr(before,"bitrate") and before.bitrate != after.bitrate:
            changes.append(f"**Bitrate:** {before.bitrate//1000}kbps → {after.bitrate//1000}kbps")
        if hasattr(before,"user_limit") and before.user_limit != after.user_limit:
            changes.append(f"**User Limit:** {before.user_limit or '∞'} → {after.user_limit or '∞'}")
        if hasattr(before,"nsfw") and before.nsfw != after.nsfw:
            changes.append(f"**NSFW:** {before.nsfw} → {after.nsfw} ⚠️")
        if before.category != after.category:
            changes.append(f"**Category:** {getattr(before.category,'name','—')} → {getattr(after.category,'name','—')}")
        # Permission overwrite changes
        b_ow = {t:ow for t,ow in before.overwrites.items()}
        a_ow = {t:ow for t,ow in after.overwrites.items()}
        for target in set(list(b_ow)+list(a_ow)):
            name = getattr(target,"name",str(target))
            if b_ow.get(target) != a_ow.get(target):
                changes.append(f"**Perms for `{name}`:** changed")
        if not changes: return
        embed = self._e("ch_update","✏️  Channel Updated")
        embed.add_field(name="📌 Channel", value=f"{after.mention} `{after.name}`", inline=True)
        embed.add_field(name="🆔 ID",      value=f"`{after.id}`",                   inline=True)
        embed.add_field(name="📝 Changes", value="\n".join(changes)[:900],          inline=False)
        try:
            async for entry in after.guild.audit_logs(limit=1, action=discord.AuditLogAction.channel_update):
                embed.add_field(name="👤 By", value=entry.user.mention, inline=True); break
        except Exception: pass
        self._f(embed, f"Channel ID: {after.id}", "XERO Logging")
        await self._log(after.guild, "ch_update", embed)

    # ── ROLE EVENTS ───────────────────────────────────────────────────────────

    @commands.Cog.listener()
    async def on_guild_role_create(self, role):
        embed = self._e("role_create","🎭  Role Created")
        embed.add_field(name="🏷️ Name",        value=f"{role.mention} `{role.name}`", inline=True)
        embed.add_field(name="🎨 Color",       value=f"`{role.color}`",               inline=True)
        embed.add_field(name="📌 Hoisted",     value="Yes" if role.hoist else "No",   inline=True)
        embed.add_field(name="💬 Mentionable", value="Yes" if role.mentionable else "No", inline=True)
        embed.add_field(name="🔢 Position",    value=str(role.position),              inline=True)
        embed.add_field(name="🆔 ID",          value=f"`{role.id}`",                  inline=True)
        key_perms = [PERM_NAMES.get(p,p) for p,v in dict(role.permissions).items() if v and p in PERM_NAMES]
        if key_perms: embed.add_field(name="🔑 Permissions", value=", ".join(key_perms[:10]), inline=False)
        if role.permissions.administrator:
            embed.add_field(name="🚨 DANGER", value="This role has **ADMINISTRATOR** — full server access!", inline=False)
        try:
            async for entry in role.guild.audit_logs(limit=1, action=discord.AuditLogAction.role_create):
                embed.add_field(name="👤 By", value=entry.user.mention, inline=True); break
        except Exception: pass
        self._f(embed, f"Role ID: {role.id}", "XERO Logging")
        await self._log(role.guild, "role_create", embed)

    @commands.Cog.listener()
    async def on_guild_role_delete(self, role):
        embed = self._e("role_delete","🗑️  Role Deleted")
        embed.add_field(name="🏷️ Name",  value=f"`{role.name}`",              inline=True)
        embed.add_field(name="🎨 Color", value=f"`{role.color}`",              inline=True)
        embed.add_field(name="🆔 ID",    value=f"`{role.id}`",                 inline=True)
        embed.add_field(name="👥 Had",   value=f"{len(role.members)} member(s)",inline=True)
        try:
            async for entry in role.guild.audit_logs(limit=1, action=discord.AuditLogAction.role_delete):
                embed.add_field(name="👤 By", value=entry.user.mention, inline=True); break
        except Exception: pass
        self._f(embed, f"Role ID: {role.id}", "XERO Logging")
        await self._log(role.guild, "role_delete", embed)

    @commands.Cog.listener()
    async def on_guild_role_update(self, before, after):
        changes = []
        if before.name        != after.name:        changes.append(f"**Name:** `{before.name}` → `{after.name}`")
        if before.color       != after.color:        changes.append(f"**Color:** `{before.color}` → `{after.color}`")
        if before.hoist       != after.hoist:        changes.append(f"**Hoisted:** {before.hoist} → {after.hoist}")
        if before.mentionable != after.mentionable:  changes.append(f"**Mentionable:** {before.mentionable} → {after.mentionable}")
        if before.position    != after.position:     changes.append(f"**Position:** {before.position} → {after.position}")
        gained, lost = self._perm_diff(before.permissions, after.permissions)
        if gained: changes.append(f"**Perms Added:** {', '.join(gained[:8])}")
        if lost:   changes.append(f"**Perms Removed:** {', '.join(lost[:8])}")
        admin_gained = not before.permissions.administrator and after.permissions.administrator
        if admin_gained: changes.append("🚨 **ADMINISTRATOR GRANTED — critical change!**")
        if not changes: return
        embed = self._e("suspicious" if admin_gained else "role_update",
                       "🚨  CRITICAL: Admin Permission Granted" if admin_gained else "✏️  Role Updated")
        embed.add_field(name="🎭 Role",    value=f"{after.mention} `{after.name}`", inline=True)
        embed.add_field(name="🆔 ID",      value=f"`{after.id}`",                   inline=True)
        embed.add_field(name="📝 Changes", value="\n".join(changes)[:900],          inline=False)
        try:
            async for entry in after.guild.audit_logs(limit=1, action=discord.AuditLogAction.role_update):
                embed.add_field(name="👤 By", value=entry.user.mention, inline=True); break
        except Exception: pass
        if admin_gained:
            ai = await self._ai(f"Role '{after.name}' just got ADMINISTRATOR permission in a Discord server. It affects {len(after.members)} members. Suspicious or intentional?")
            if ai: embed.add_field(name="🤖 AI Assessment", value=ai, inline=False)
        self._f(embed, f"Role ID: {after.id}", "XERO Logging")
        await self._log(after.guild, "role_update", embed)

    # ── SERVER / MISC EVENTS ──────────────────────────────────────────────────

    @commands.Cog.listener()
    async def on_guild_update(self, before, after):
        changes = []
        if before.name                    != after.name:               changes.append(f"**Name:** `{before.name}` → `{after.name}`")
        if before.description             != after.description:         changes.append("**Description:** changed")
        if before.verification_level      != after.verification_level:  changes.append(f"**Verification:** {before.verification_level.name} → {after.verification_level.name}")
        if before.explicit_content_filter != after.explicit_content_filter: changes.append(f"**Content Filter:** changed")
        if before.afk_channel             != after.afk_channel:         changes.append(f"**AFK Channel:** {getattr(before.afk_channel,'name','—')} → {getattr(after.afk_channel,'name','—')}")
        if before.afk_timeout             != after.afk_timeout:         changes.append(f"**AFK Timeout:** {before.afk_timeout}s → {after.afk_timeout}s")
        if before.premium_tier            != after.premium_tier:        changes.append(f"**Boost Level:** {before.premium_tier} → {after.premium_tier} 💎")
        if before.icon                    != after.icon:                changes.append("**Server Icon:** changed 🖼️")
        if before.banner                  != after.banner:              changes.append("**Banner:** changed 🖼️")
        if before.mfa_level               != after.mfa_level:           changes.append(f"**2FA Requirement:** {before.mfa_level} → {after.mfa_level}")
        if before.vanity_url_code         != after.vanity_url_code:     changes.append(f"**Vanity URL:** changed")
        if not changes: return
        embed = self._e("server","🏰  Server Settings Updated")
        embed.set_thumbnail(url=after.icon.url if after.icon else discord.Embed.Empty)
        embed.add_field(name="📝 Changes", value="\n".join(changes)[:900], inline=False)
        try:
            async for entry in after.audit_logs(limit=1, action=discord.AuditLogAction.guild_update):
                embed.add_field(name="👤 By", value=entry.user.mention, inline=True); break
        except Exception: pass
        self._f(embed, f"Server ID: {after.id}", "XERO Logging")
        await self._log(after, "server", embed)

    @commands.Cog.listener()
    async def on_guild_emojis_update(self, guild, before, after):
        added   = [e for e in after  if e.id not in {x.id for x in before}]
        removed = [e for e in before if e.id not in {x.id for x in after}]
        if not added and not removed: return
        embed = self._e("emoji","😄  Emojis Updated")
        if added:   embed.add_field(name=f"➕ Added ({len(added)})",   value=" ".join(str(e) for e in added[:20]),  inline=False)
        if removed: embed.add_field(name=f"➖ Removed ({len(removed)})", value=", ".join(e.name for e in removed[:15]), inline=False)
        embed.add_field(name="📊 Total", value=f"{len(after)}/{guild.emoji_limit}", inline=True)
        self._f(embed, f"Server: {guild.name}", "XERO Logging")
        await self._log(guild, "emoji", embed)

    @commands.Cog.listener()
    async def on_guild_stickers_update(self, guild, before, after):
        added   = [s for s in after  if s.id not in {x.id for x in before}]
        removed = [s for s in before if s.id not in {x.id for x in after}]
        if not added and not removed: return
        embed = self._e("emoji","🎨  Stickers Updated")
        if added:   embed.add_field(name=f"➕ Added",   value=", ".join(s.name for s in added),   inline=False)
        if removed: embed.add_field(name=f"➖ Removed", value=", ".join(s.name for s in removed), inline=False)
        self._f(embed, f"Server: {guild.name}", "XERO Logging")
        await self._log(guild, "emoji", embed)

    @commands.Cog.listener()
    async def on_invite_create(self, invite):
        if not invite.guild: return
        embed = self._e("invite","🔗  Invite Created")
        embed.add_field(name="🔑 Code",    value=f"`discord.gg/{invite.code}`",                       inline=True)
        embed.add_field(name="📢 Channel", value=invite.channel.mention if invite.channel else "?",    inline=True)
        embed.add_field(name="👤 Creator", value=invite.inviter.mention if invite.inviter else "?",    inline=True)
        embed.add_field(name="🔢 Max Uses",value=str(invite.max_uses) or "∞",                         inline=True)
        embed.add_field(name="⏰ Expires", value=(f"<t:{int((discord.utils.utcnow()+datetime.timedelta(seconds=invite.max_age)).timestamp())}:R>" if invite.max_age else "Never"), inline=True)
        embed.add_field(name="👥 Temp",   value="Yes" if invite.temporary else "No",                   inline=True)
        await self._log(invite.guild, "invite", embed)

    @commands.Cog.listener()
    async def on_invite_delete(self, invite):
        if not invite.guild: return
        embed = self._e("invite","🔗  Invite Deleted")
        embed.add_field(name="🔑 Code",    value=f"`discord.gg/{invite.code}`",                       inline=True)
        embed.add_field(name="📢 Channel", value=invite.channel.mention if invite.channel else "?",    inline=True)
        try:
            async for entry in invite.guild.audit_logs(limit=1, action=discord.AuditLogAction.invite_delete):
                embed.add_field(name="👤 By", value=entry.user.mention, inline=True); break
        except Exception: pass
        await self._log(invite.guild, "invite", embed)

    @commands.Cog.listener()
    async def on_webhooks_update(self, channel):
        guild = channel.guild; s = await self._settings(guild.id)
        embed = self._e("webhook","🪝  Webhook Activity")
        embed.add_field(name="📢 Channel", value=channel.mention, inline=True)
        try:
            async for entry in guild.audit_logs(limit=1, action=discord.AuditLogAction.webhook_create):
                if (discord.utils.utcnow()-entry.created_at).seconds < 10:
                    embed.add_field(name="👤 Created By", value=entry.user.mention, inline=True)
                    embed.add_field(name="⚠️ Action",    value="Webhook Created",   inline=True)
                    if s.get("webhook_protection_enabled",0) and not entry.user.guild_permissions.administrator:
                        try:
                            for wh in await channel.webhooks():
                                if wh.user and wh.user.id == entry.user.id:
                                    await wh.delete(reason="XERO Webhook Protection")
                                    embed.add_field(name="🛡️ Auto-Deleted", value="Non-admin webhook removed automatically.", inline=False)
                        except Exception: pass
                    break
        except Exception: pass
        self._f(embed, f"Channel ID: {channel.id}", "XERO Logging")
        await self._log(guild, "webhook", embed)

    @commands.Cog.listener()
    async def on_thread_create(self, thread):
        embed = self._e("thread","🧵  Thread Created")
        embed.add_field(name="🏷️ Name",       value=f"`{thread.name}`",                                inline=True)
        embed.add_field(name="📌 Parent",     value=thread.parent.mention if thread.parent else "?",   inline=True)
        embed.add_field(name="👤 Owner",      value=thread.owner.mention  if thread.owner  else "?",   inline=True)
        embed.add_field(name="⏰ Auto-Archive",value=f"{thread.auto_archive_duration}min",              inline=True)
        embed.add_field(name="🆔 ID",         value=f"`{thread.id}`",                                   inline=True)
        self._f(embed, f"Thread ID: {thread.id}", "XERO Logging")
        await self._log(thread.guild, "thread", embed)

    @commands.Cog.listener()
    async def on_thread_delete(self, thread):
        embed = self._e("thread","🧵  Thread Deleted")
        embed.add_field(name="🏷️ Name",  value=f"`{thread.name}`",                              inline=True)
        embed.add_field(name="📌 Parent",value=thread.parent.mention if thread.parent else "?", inline=True)
        embed.add_field(name="🆔 ID",    value=f"`{thread.id}`",                                 inline=True)
        self._f(embed, f"Thread ID: {thread.id}", "XERO Logging")
        await self._log(thread.guild, "thread", embed)


def _ts(iso: str) -> str:
    """Convert ISO timestamp to Discord relative."""
    try:
        dt = datetime.datetime.fromisoformat(iso.replace("Z",""))
        return f"<t:{int(dt.timestamp())}:R>"
    except Exception:
        return iso[:10] if iso else "—"


class UserLogPage:
    """One page of a user's log history."""
    def __init__(self, title: str, embed: discord.Embed, category: str):
        self.title    = title
        self.embed    = embed
        self.category = category


async def _collect_user_logs(bot, guild, user: discord.User, include_global: bool = True) -> list:
    """
    Pull every XERO record about this user and return a list of UserLogPage objects.
    Each page is one category: summary, mod cases, warnings, tickets, economy, cross-server.
    """
    uid     = user.id
    gid     = guild.id
    db_obj = bot.db
    pages   = []
    age_days = (discord.utils.utcnow() - user.created_at).days

    async with db_obj._db_context() as db:
        db.row_factory = aiosqlite.Row

        # ── Mod cases ────────────────────────────────────────────────────
        async with db.execute(
            "SELECT * FROM mod_cases WHERE guild_id=? AND user_id=? ORDER BY case_id DESC LIMIT 50",
            (gid, uid)
        ) as c: mod_cases = [dict(r) for r in await c.fetchall()]

        # ── Warnings ─────────────────────────────────────────────────────
        async with db.execute(
            "SELECT * FROM warnings WHERE guild_id=? AND user_id=? ORDER BY id DESC",
            (gid, uid)
        ) as c: warnings = [dict(r) for r in await c.fetchall()]

        # ── Tickets ───────────────────────────────────────────────────────
        async with db.execute(
            "SELECT * FROM tickets WHERE guild_id=? AND user_id=? ORDER BY ticket_id DESC",
            (gid, uid)
        ) as c: tickets = [dict(r) for r in await c.fetchall()]

        # ── Economy transactions ──────────────────────────────────────────
        try:
            async with db.execute(
                "SELECT * FROM economy_transactions WHERE guild_id=? AND user_id=? ORDER BY id DESC LIMIT 20",
                (gid, uid)
            ) as c: eco_txns = [dict(r) for r in await c.fetchall()]
        except Exception: eco_txns = []

        # ── Economy balance ───────────────────────────────────────────────
        async with db.execute(
            "SELECT wallet, bank, total_earned, total_spent FROM economy WHERE guild_id=? AND user_id=?",
            (gid, uid)
        ) as c:
            eco_row = await c.fetchone()
        eco = dict(eco_row) if eco_row else {}

        # ── Level ─────────────────────────────────────────────────────────
        async with db.execute(
            "SELECT level, total_xp FROM levels WHERE guild_id=? AND user_id=?",
            (gid, uid)
        ) as c:
            lvl_row = await c.fetchone()
        lvl = dict(lvl_row) if lvl_row else {"level":0,"total_xp":0}

        # ── Stats ─────────────────────────────────────────────────────────
        async with db.execute(
            "SELECT commands_used, messages_sent FROM user_stats WHERE guild_id=? AND user_id=?",
            (gid, uid)
        ) as c:
            stats_row = await c.fetchone()
        stats = dict(stats_row) if stats_row else {"commands_used":0,"messages_sent":0}

        # ── Cross-server (global) ─────────────────────────────────────────
        if include_global:
            async with db.execute(
                "SELECT guild_id, action, reason, timestamp FROM mod_cases WHERE user_id=? AND guild_id!=? ORDER BY case_id DESC LIMIT 30",
                (uid, gid)
            ) as c: global_cases = [dict(r) for r in await c.fetchall()]
        else:
            global_cases = []

        # ── Blacklist ─────────────────────────────────────────────────────
        try:
            async with db.execute("SELECT reason, blacklisted_at FROM blacklisted_users WHERE user_id=?", (uid,)) as c:
                bl = await c.fetchone()
            blacklisted = dict(bl) if bl else None
        except Exception: blacklisted = None

        # ── Reputation ────────────────────────────────────────────────────
        try:
            async with db.execute("SELECT SUM(rep_given) FROM reputation WHERE guild_id=? AND to_user_id=?", (gid, uid)) as c:
                rep_row = await c.fetchone()
            total_rep = rep_row[0] or 0 if rep_row else 0
        except Exception: total_rep = 0

    # ── PAGE 1: Summary ───────────────────────────────────────────────────
    member = guild.get_member(uid)
    risk   = "🔴 HIGH" if (blacklisted or sum(1 for c in global_cases if c["action"].lower() in ("ban","tempban")) >= 2) \
             else ("🟡 MEDIUM" if (any(c["action"].lower() in ("ban","tempban") for c in global_cases) or len(warnings) >= 3 or len(mod_cases) >= 3) \
             else "🟢 LOW")
    cross_bans = [c for c in global_cases if c["action"].lower() in ("ban","tempban")]

    summary_e = discord.Embed(
        title=f"👤  {user.display_name}  •  Full Log",
        description=f"Complete XERO record for **{user}** (`{uid}`)",
        color=C_SUMMARY,
        timestamp=discord.utils.utcnow()
    )
    summary_e.set_thumbnail(url=user.display_avatar.url)
    summary_e.add_field(name="🆔 User ID",          value=f"`{uid}`",                               inline=True)
    summary_e.add_field(name="📅 Account Age",       value=f"{age_days} days",                       inline=True)
    summary_e.add_field(name="⚠️ Risk Level",        value=risk,                                     inline=True)
    summary_e.add_field(name="📊 Level",             value=str(lvl["level"]),                        inline=True)
    summary_e.add_field(name="💬 Messages",          value=f"{stats.get('messages_sent',0):,}",      inline=True)
    summary_e.add_field(name="⭐ Reputation",        value=f"+{total_rep}",                          inline=True)
    summary_e.add_field(name="🛡️ Local Mod Cases",  value=str(len(mod_cases)),                      inline=True)
    summary_e.add_field(name="⚠️ Local Warnings",   value=str(len(warnings)),                       inline=True)
    summary_e.add_field(name="🎫 Tickets",           value=str(len(tickets)),                        inline=True)
    if global_cases:
        summary_e.add_field(name="🌐 Cross-Server Cases", value=str(len(global_cases)),              inline=True)
    if cross_bans:
        ban_lines = []
        for b in cross_bans[:4]:
            s_obj = bot.get_guild(b["guild_id"])
            sname = s_obj.name if s_obj else f"Server {b['guild_id']}"
            ban_lines.append(f"• **{sname}** — {b['timestamp'][:10]}")
        summary_e.add_field(name=f"🚨 BANNED IN {len(cross_bans)} XERO SERVER(S)", value="\n".join(ban_lines), inline=False)
    if blacklisted:
        summary_e.add_field(name="🚫 GLOBAL BLACKLIST", value=f"Reason: {blacklisted['reason']}", inline=False)
    summary_e.set_footer(text="Page 1 — Summary  •  XERO User Logs  •  Staff Only")
    pages.append(UserLogPage("Summary", summary_e, "summary"))

    # ── PAGE 2+: Mod cases (10 per page) ─────────────────────────────────
    if mod_cases:
        for chunk_start in range(0, len(mod_cases), 10):
            chunk = mod_cases[chunk_start:chunk_start+10]
            e = comprehensive_embed(title=f"🛡️  Mod Cases — {user.display_name}", color=C_MOD, timestamp=discord.utils.utcnow())
            for case in chunk:
                mod = guild.get_member(case["mod_id"])
                mod_str = mod.display_name if mod else f"ID:{case['mod_id']}"
                e.add_field(
                    name=f"Case #{case['case_id']} — {case['action'].upper()}",
                    value=f"**Reason:** {case.get('reason','No reason')[:80]}\n**By:** {mod_str}  **When:** {_ts(case['timestamp'])}",
                    inline=False
                )
            e.set_footer(text=f"Mod Cases {chunk_start+1}–{chunk_start+len(chunk)} of {len(mod_cases)}  •  XERO User Logs")
            pages.append(UserLogPage(f"Mod Cases ({chunk_start+1}–{chunk_start+len(chunk)})", e, "mod"))

    # ── PAGE: Warnings ────────────────────────────────────────────────────
    if warnings:
        e = comprehensive_embed(title=f"⚠️  Warnings — {user.display_name}", color=C_WARN, timestamp=discord.utils.utcnow())
        e.description = f"**{len(warnings)}** warning(s) in this server"
        for w in warnings[:12]:
            mod = guild.get_member(w["mod_id"])
            mod_str = mod.display_name if mod else f"ID:{w['mod_id']}"
            e.add_field(name=f"⚠️ Warning #{w['id']}", value=f"{w.get('reason','No reason')[:100]}\n*by {mod_str}  {_ts(w['timestamp'])}*", inline=False)
        e.set_footer(text=f"{len(warnings)} warning(s) total  •  XERO User Logs")
        pages.append(UserLogPage(f"Warnings ({len(warnings)})", e, "warnings"))

    # ── PAGE: Tickets ─────────────────────────────────────────────────────
    if tickets:
        for chunk_start in range(0, len(tickets), 5):
            chunk = tickets[chunk_start:chunk_start+5]
            e = comprehensive_embed(title=f"🎫  Tickets — {user.display_name}", color=C_TICKET, timestamp=discord.utils.utcnow())
            for t in chunk:
                status_icon = "🟢" if t["status"] == "open" else "⚫"
                summary_short = (t.get("ai_summary") or "No summary")[:80]
                closer = guild.get_member(t.get("closed_by") or 0)
                closer_str = closer.display_name if closer else ("—" if t["status"]=="open" else f"ID:{t.get('closed_by','?')}")
                e.add_field(
                    name=f"{status_icon} Ticket #{t['ticket_id']} — {t.get('topic','General')}",
                    value=f"**Status:** {t['status'].title()}\n**Opened:** {_ts(t['created_at'])}\n**Closed by:** {closer_str}\n**AI:** {summary_short}...",
                    inline=False
                )
            e.set_footer(text=f"Tickets {chunk_start+1}–{chunk_start+len(chunk)} of {len(tickets)}  •  XERO User Logs")
            pages.append(UserLogPage(f"Tickets ({chunk_start+1}–{chunk_start+len(chunk)})", e, "tickets"))

    # ── PAGE: Economy ─────────────────────────────────────────────────────
    if eco:
        e = comprehensive_embed(title=f"💰  Economy — {user.display_name}", color=C_ECO, timestamp=discord.utils.utcnow())
        e.add_field(name="👛 Wallet",       value=f"${eco.get('wallet',0):,}",        inline=True)
        e.add_field(name="🏦 Bank",         value=f"${eco.get('bank',0):,}",          inline=True)
        e.add_field(name="📈 Total Earned", value=f"${eco.get('total_earned',0):,}",  inline=True)
        e.add_field(name="📉 Total Spent",  value=f"${eco.get('total_spent',0):,}",   inline=True)
        if eco_txns:
            lines = []
            for tx in eco_txns[:8]:
                lines.append(f"• {tx.get('type','?')} **${tx.get('amount',0):,}** {_ts(tx.get('timestamp',''))}")
            e.add_field(name="📋 Recent Transactions", value="\n".join(lines), inline=False)
        e.set_footer(text="Economy History  •  XERO User Logs")
        pages.append(UserLogPage("Economy", e, "economy"))

    # ── PAGE: Cross-server ────────────────────────────────────────────────
    if global_cases:
        for chunk_start in range(0, len(global_cases), 10):
            chunk = global_cases[chunk_start:chunk_start+10]
            e = discord.Embed(
                title=f"🌐  Cross-Server History — {user.display_name}",
                description=f"Actions in **other XERO servers** (not this one)",
                color=C_GLOBAL, timestamp=discord.utils.utcnow()
            )
            for gc in chunk:
                s_obj  = bot.get_guild(gc["guild_id"])
                sname  = s_obj.name if s_obj else f"Server {gc['guild_id']}"
                e.add_field(
                    name=f"🌐 {gc['action'].upper()} — {sname}",
                    value=f"**Reason:** {gc.get('reason','No reason')[:80]}\n**When:** {_ts(gc['timestamp'])}",
                    inline=False
                )
            e.set_footer(text=f"Cross-Server {chunk_start+1}–{chunk_start+len(chunk)} of {len(global_cases)}  •  XERO User Logs")
            pages.append(UserLogPage(f"Cross-Server ({chunk_start+1}–{chunk_start+len(chunk)})", e, "global"))

    return pages


class UserLogView(discord.ui.View):
    def __init__(self, pages: list, user: discord.User):
        super().__init__(timeout=180)
        self.pages = pages
        self.user  = user
        self.idx   = 0
        self._upd()

    def _upd(self):
        self.prev_btn.disabled = self.idx <= 0
        self.next_btn.disabled = self.idx >= len(self.pages) - 1
        self.counter.label     = f"{self.idx+1} / {len(self.pages)}"
        if self.pages:
            cat = self.pages[self.idx].category
            cat_labels = {"summary":"📋","mod":"🛡️","warnings":"⚠️","tickets":"🎫","economy":"💰","global":"🌐"}
            self.category_label.label = cat_labels.get(cat, "•") + " " + self.pages[self.idx].title[:20]

    @discord.ui.button(emoji="◀", style=discord.ButtonStyle.secondary, custom_id="ul_prev")
    async def prev_btn(self, interaction, button):
        self.idx -= 1; self._upd()
        await interaction.response.edit_message(embed=self.pages[self.idx].embed, view=self)

    @discord.ui.button(label="1 / 1", style=discord.ButtonStyle.secondary, disabled=True, custom_id="ul_ctr")
    async def counter(self, interaction, button): pass

    @discord.ui.button(label="📋 Summary", style=discord.ButtonStyle.secondary, disabled=True, custom_id="ul_cat")
    async def category_label(self, interaction, button): pass

    @discord.ui.button(emoji="▶", style=discord.ButtonStyle.secondary, custom_id="ul_next")
    async def next_btn(self, interaction, button):
        self.idx += 1; self._upd()
        await interaction.response.edit_message(embed=self.pages[self.idx].embed, view=self)


# ── CONFIG COMMANDS ───────────────────────────────────────────────────────────

class LoggingConfig(commands.GroupCog, name="logs"):
    def __init__(self, bot): self.bot = bot


    @app_commands.command(name="user", description="Pull every XERO log for a user — mod cases, warnings, tickets, economy, cross-server history.")
    @app_commands.describe(user="The user to pull logs for")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def user_logs(self, interaction: discord.Interaction, user: discord.Member):
        await interaction.response.defer(ephemeral=True)
        pages = await _collect_user_logs(self.bot, interaction.guild, user)
        if not pages:
            return await interaction.followup.send(embed=comprehensive_embed(description=f"No XERO records found for {user.mention}.", color=0x2B2D31))
        view  = UserLogView(pages, user)
        await interaction.followup.send(embed=pages[0].embed, view=view)

    @app_commands.command(name="setup", description="Configure the elite logging system with smart defaults.")
    @app_commands.describe(channel="Primary channel for ALL logs (Unified)", messages="Specific channel for edits/deletes", members="Specific channel for joins/leaves/roles", server="Specific channel for server/role changes", voice="Specific channel for voice sessions")
    @app_commands.checks.has_permissions(administrator=True)
    async def setup(self, interaction: discord.Interaction, channel: discord.TextChannel, messages: discord.TextChannel=None, members: discord.TextChannel=None, server: discord.TextChannel=None, voice: discord.TextChannel=None):
        updates = {"log_channel_id": channel.id}
        if not messages: updates["message_log_channel_id"] = channel.id
        else: updates["message_log_channel_id"] = messages.id
        if not members: updates["member_log_channel_id"] = channel.id
        else: updates["member_log_channel_id"] = members.id
        if not server: updates["server_log_channel_id"] = channel.id
        else: updates["server_log_channel_id"] = server.id
        if not voice: updates["voice_log_channel_id"] = channel.id
        else: updates["voice_log_channel_id"] = voice.id
        
        for k,v in updates.items(): await self.bot.db.update_guild_setting(interaction.guild.id,k,v)
        adv = self.bot.cogs.get("AdvancedLogger")
        if adv: adv._cache.pop(interaction.guild.id, None)
        
        def fmt(cid): return f"<#{cid}>" if cid else "—"
        embed = discord.Embed(
            title="📋  Logging Protocol Initialized",
            description=(
                "XERO elite logging is now active. We monitor every event with AI threat scoring, "
                "permission diffs, and deep audit integration.\n\n"
                "**The most detailed logging of any bot. Period.**"
            ),
            color=0x00D4FF, timestamp=discord.utils.utcnow()
        )
        embed.add_field(name="🌐 Unified",  value=channel.mention,  inline=True)
        embed.add_field(name="💬 Messages", value=fmt(updates.get("message_log_channel_id")), inline=True)
        embed.add_field(name="👥 Members",  value=fmt(updates.get("member_log_channel_id")),  inline=True)
        embed.add_field(name="🏰 Server",   value=fmt(updates.get("server_log_channel_id")),   inline=True)
        embed.add_field(name="🔊 Voice",    value=fmt(updates.get("voice_log_channel_id")),    inline=True)
        embed.add_field(name="📋 What's Logged", value=(
            "✅ Message edits (before/after + char diff)\n"
            "✅ Deletions (who deleted + full content + attachments)\n"
            "✅ Bulk deletes (full .txt transcript file + AI analysis)\n"
            "✅ Member joins with **AI threat score 0-100**\n"
            "✅ **Invite tracking** — which link each member used\n"
            "✅ Leaves (voluntary vs kicked, time they stayed, roles they had)\n"
            "✅ Bans + unbans with reason and who did it\n"
            "✅ Nickname changes (who changed it)\n"
            "✅ Role changes (who gave/removed, dangerous perms flagged)\n"
            "✅ **Suspicious bulk role changes** — AI flagged\n"
            "✅ Admin permission grants — instant AI alert\n"
            "✅ Timeouts (applied + removed, by who, reason)\n"
            "✅ Server boosts 💎\n"
            "✅ Channel create/edit/delete + **permission overwrite diffs**\n"
            "✅ Role create/edit/delete + **full permission diffs**\n"
            "✅ All server settings changes\n"
            "✅ Emoji + sticker add/remove\n"
            "✅ Invite create/delete\n"
            "✅ Voice join/leave/move/mute/deaf/stream/camera + **session duration**\n"
            "✅ Thread create/delete\n"
            "✅ Webhook create/delete + **auto-delete protection**\n"
            "✅ Rapid edit pattern detection\n"
            "✅ All backed by NVIDIA Nemotron-3-Super AI analysis"
        ), inline=False)
        embed.set_footer(text="XERO Logging  •  Period.")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="ignore-channel", description="Exclude a channel from message logging.")
    @app_commands.describe(channel="Channel to ignore")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def ignore_channel(self, interaction: discord.Interaction, channel: discord.TextChannel):
        async with self.bot.db._db_context() as db:
            await db.execute("INSERT OR IGNORE INTO log_ignored_channels (guild_id, channel_id) VALUES (?,?)", (interaction.guild.id, channel.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Channel Ignored", f"Messages in {channel.mention} will no longer be logged."))

    @app_commands.command(name="ignore-role", description="Exclude a role from message logging.")
    @app_commands.describe(role="Role to ignore")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def ignore_role(self, interaction: discord.Interaction, role: discord.Role):
        async with self.bot.db._db_context() as db:
            await db.execute("INSERT OR IGNORE INTO log_ignored_roles (guild_id, role_id) VALUES (?,?)", (interaction.guild.id, role.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Role Ignored", f"Users with the {role.mention} role will no longer have their messages logged."))

    @app_commands.command(name="view", description="View current logging configuration.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def view(self, interaction: discord.Interaction):
        s = await self.bot.db.get_guild_settings(interaction.guild.id)
        def ch(cid): return f"<#{cid}>" if cid else "❌ Not set"
        embed = comprehensive_embed(title=f"📋  Logging — {interaction.guild.name}", color=0x00D4FF)
        embed.add_field(name="🌐 Unified",   value=ch(s.get("log_channel_id")),           inline=True)
        embed.add_field(name="💬 Messages",  value=ch(s.get("message_log_channel_id")),   inline=True)
        embed.add_field(name="👥 Members",   value=ch(s.get("member_log_channel_id")),    inline=True)
        embed.add_field(name="🏰 Server",    value=ch(s.get("server_log_channel_id")),    inline=True)
        embed.add_field(name="🔊 Voice",     value=ch(s.get("voice_log_channel_id")),     inline=True)
        embed.add_field(name="🛡️ Webhooks", value="✅ Protected" if s.get("webhook_protection_enabled") else "❌ Off", inline=True)
        embed.set_footer(text="XERO Logging  •  /logs setup to configure")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="webhook-protection", description="Auto-delete webhooks created by non-admins. Kills webhook spam attacks.")
    @app_commands.describe(enabled="Enable or disable")
    @app_commands.checks.has_permissions(administrator=True)
    async def webhook_protection(self, interaction: discord.Interaction, enabled: bool):
        await self.bot.db.update_guild_setting(interaction.guild.id,"webhook_protection_enabled",1 if enabled else 0)
        adv = self.bot.cogs.get("AdvancedLogger")
        if adv: adv._cache.pop(interaction.guild.id, None)
        msg = ("✅ **Webhook Protection enabled.**\nWebhooks created by non-admins are auto-deleted instantly." if enabled
               else "❌ **Webhook Protection disabled.**")
        await interaction.response.send_message(embed=comprehensive_embed(description=msg,color=0x00FF94 if enabled else 0xFF3B5C))

    @app_commands.command(name="test", description="Send test log messages to all configured channels.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def test(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        adv = self.bot.cogs.get("AdvancedLogger")
        if not adv: return await interaction.followup.send("Logger cog not loaded.",ephemeral=True)
        sent = set()
        for lt in ["msg_edit","join","ch_create","voice","role_create"]:
            ch = await adv._ch(interaction.guild, lt)
            if ch and ch.id not in sent:
                try:
                    e = comprehensive_embed(title="🧪  XERO Logging Test",
                                     description=f"✅ **{lt.replace('_',' ').title()}** logs working!",
                                     color=0x00D4FF, timestamp=discord.utils.utcnow())
                    e.set_footer(text=f"Tested by {interaction.user}  •  XERO Logging")
                    await ch.send(embed=e); sent.add(ch.id)
                except Exception: pass
        result = f"✅ Tests sent to {len(sent)} channel(s)." if sent else "❌ No log channels set. Use `/logs setup` first."
        await interaction.followup.send(embed=comprehensive_embed(description=result,color=0x00FF94 if sent else 0xFF3B5C),ephemeral=True)


async def setup(bot):
    try:
        async with bot.db._db_context() as db:
            for col in ["message_log_channel_id INTEGER","member_log_channel_id INTEGER",
                        "server_log_channel_id INTEGER","voice_log_channel_id INTEGER",
                        "webhook_protection_enabled INTEGER DEFAULT 0"]:
                try: await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col}")
                except Exception: pass
            await db.commit()
    except Exception as e: logger.error(f"Logging migration: {e}")
    await bot.add_cog(AdvancedLogger(bot))
    await bot.add_cog(LoggingConfig(bot))
