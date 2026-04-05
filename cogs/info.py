"""
XERO Bot — /info Command Group
All information commands in one clean, consistent, hyper-detailed group.
Replaces: userinfo, serverinfo, roleinfo, channelinfo, botinfo (scattered across utility/server/profile)
"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
import datetime
import platform
import time
try:
    import psutil
    HAS_PSUTIL = True
except ImportError:
    HAS_PSUTIL = False
import os
from utils.embeds import comprehensive_embed, info_embed, error_embed

logger = logging.getLogger("XERO.Info")


class Info(commands.GroupCog, name="info"):
    """All /info subcommands in one place."""

    def __init__(self, bot):
        self.bot = bot

    # ── /info user ────────────────────────────────────────────────────────
    @app_commands.command(name="user", description="Get the most detailed breakdown of any user — account, server stats, level, economy, mod history.")
    @app_commands.describe(user="User to inspect (defaults to yourself)")
    @command_guard
    async def user(self, interaction: discord.Interaction, user: discord.Member = None):
        target = user or interaction.user
        await interaction.response.defer()

        # Parallel data fetch
        level_data  = await self.bot.db.get_level(target.id, interaction.guild.id)
        eco_data    = await self.bot.db.get_economy(target.id, interaction.guild.id)
        stats_data  = await self.bot.db.get_user_stats(target.id, interaction.guild.id)
        warnings    = await self.bot.db.get_warnings(interaction.guild.id, target.id)
        cases       = await self.bot.db.get_mod_cases(interaction.guild.id, target.id, limit=3)

        # Derived values
        level     = level_data.get("level", 0)
        total_xp  = level_data.get("total_xp", 0)
        curr_xp   = level_data.get("xp", 0)
        next_xp   = ((level + 1) ** 2) * 100
        wallet    = eco_data.get("wallet", 0)
        bank      = eco_data.get("bank", 0)
        net_worth = wallet + bank

        # XP progress bar
        bar_fill  = min(int((curr_xp / max(next_xp, 1)) * 15), 15)
        xp_bar    = "█" * bar_fill + "░" * (15 - bar_fill)

        # Badges
        badges = []
        if target.id == interaction.guild.owner_id:     badges.append("👑 Owner")
        if target.guild_permissions.administrator:       badges.append("🛡️ Admin")
        if target.guild_permissions.manage_guild:        badges.append("⚙️ Manager")
        if target.guild_permissions.manage_messages:     badges.append("🔨 Moderator")
        if target.premium_since:                         badges.append("💎 Booster")
        if target.bot:                                   badges.append("🤖 Bot")
        if level >= 50:                                  badges.append("🔥 Legend")
        if level >= 25:                                  badges.append("⭐ Veteran")
        if net_worth >= 1_000_000:                       badges.append("🤑 Millionaire")

        # Status
        status_icons = {
            discord.Status.online:    "🟢 Online",
            discord.Status.idle:      "🟡 Idle",
            discord.Status.dnd:       "🔴 Do Not Disturb",
            discord.Status.offline:   "⚫ Offline",
        }

        desc = (
            f"**Account Identity**\n"
            f"──────────────────────────\n"
            f"**User**\n{target.mention} (`{target.id}`)\n"
            f"──────────────────────────\n"
            f"**Server Presence**\n"
            f"Joined: <t:{int(target.joined_at.timestamp())}:D>\n"
            f"Top Role: {target.top_role.mention}\n"
            f"Status: {status_icons.get(target.status, '⚫ Unknown')}\n"
            f"──────────────────────────\n"
            f"**Experience & Progression**\n"
            f"Level: {level} | Total XP: {total_xp:,}\n"
            f"`{xp_bar}`\n"
            f"──────────────────────────\n"
            f"**Economy & Assets**\n"
            f"Wallet: `${wallet:,}` | Bank: `${bank:,}`\n"
            f"Net Worth: **`${net_worth:,}`**\n"
            f"──────────────────────────\n"
            f"**Activity Metrics**\n"
            f"Commands: {stats_data.get('commands_used', 0):,} | Messages: {stats_data.get('messages_sent', 0):,}\n"
            f"Warnings: {len(warnings)}"
        )

        embed = comprehensive_embed(
            title=f"{'  '.join(badges)}" if badges else f"USER PROFILE: {target.display_name}",
            description=f"**ELITE DOSSIER — {target.display_name.upper()}**\n\n{desc}",
            color=target.color if target.color.value else XERO.PRIMARY,
            thumbnail=target.display_avatar.url,
            author_name=f"{target} — ELITE DOSSIER",
            author_icon=target.display_avatar.url
        )
        
        from utils.embeds import brand_embed, comprehensive_embed
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        await interaction.followup.send(embed=embed, file=file)

    # ── /info server ──────────────────────────────────────────────────────
    @app_commands.command(name="server", description="Complete server breakdown — members, channels, boosts, security, activity stats.")
    @command_guard
    async def server(self, interaction: discord.Interaction):
        await interaction.response.defer()
        g = interaction.guild

        # Fetch DB stats
        import aiosqlite
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT SUM(commands_used), SUM(messages_sent) FROM user_stats WHERE guild_id=?", (g.id,)) as c:
                stat_row = await c.fetchone()
            async with db.execute("SELECT COUNT(*) FROM mod_cases WHERE guild_id=?", (g.id,)) as c:
                mod_cases = (await c.fetchone())[0]
            async with db.execute("SELECT COUNT(*) FROM levels WHERE guild_id=? AND level > 0", (g.id,)) as c:
                leveled_members = (await c.fetchone())[0]

        total_cmds  = stat_row[0] or 0
        total_msgs  = stat_row[1] or 0

        # Channel breakdown
        text_ch   = [c for c in g.channels if isinstance(c, discord.TextChannel)]
        voice_ch  = [c for c in g.channels if isinstance(c, discord.VoiceChannel)]
        stage_ch  = [c for c in g.channels if isinstance(c, discord.StageChannel)]
        forum_ch  = [c for c in g.channels if isinstance(c, discord.ForumChannel)]

        # Member breakdown
        humans  = sum(1 for m in g.members if not m.bot)
        bots    = sum(1 for m in g.members if m.bot)
        online  = sum(1 for m in g.members if m.status == discord.Status.online)
        idle    = sum(1 for m in g.members if m.status == discord.Status.idle)
        dnd     = sum(1 for m in g.members if m.status == discord.Status.dnd)

        # Boost perks
        boost_perks = {0: "None", 1: "50 emojis, 128kbps audio", 2: "150 emojis, 256kbps, banner", 3: "250 emojis, 384kbps, vanity URL"}

        desc = (
            f"**Server Identity**\n"
            f"──────────────────────────\n"
            f"**Owner**\n{g.owner.mention if g.owner else 'Unknown'} (`{g.id}`)\n"
            f"──────────────────────────\n"
            f"**Member Breakdown**\n"
            f"Total: {g.member_count:,} | Humans: {humans:,} | Bots: {bots:,}\n"
            f"🟢 {online} | 🟡 {idle} | 🔴 {dnd}\n"
            f"──────────────────────────\n"
            f"**Channel Infrastructure**\n"
            f"Text: {len(text_ch)} | Voice: {len(voice_ch)} | Forum: {len(forum_ch)}\n"
            f"──────────────────────────\n"
            f"**Boost Status**\n"
            f"Level: {g.premium_tier} | Boosts: {g.premium_subscription_count}\n"
            f"──────────────────────────\n"
            f"**Security & Verification**\n"
            f"Level: {g.verification_level.name.replace('_', ' ').title()}\n"
            f"──────────────────────────\n"
            f"**XERO Activity Metrics**\n"
            f"Commands: {total_cmds:,} | Messages: {total_msgs:,}\n"
            f"Mod Cases: {mod_cases:,} | Leveled Members: {leveled_members:,}"
        )

        embed = comprehensive_embed(
            title=f"SERVER OVERVIEW — {g.name.upper()}",
            description=f"**ELITE SERVER DOSSIER**\n\n{desc}",
            color=XERO.PRIMARY,
            thumbnail=g.icon.url if g.icon else None,
            author_name=f"{g.name} — SERVER INFO",
            author_icon=g.icon.url if g.icon else None
        )
        
        from utils.embeds import brand_embed
        embed, file = await brand_embed(embed, g, self.bot)
        await interaction.followup.send(embed=embed, file=file)

    # ── /info role ────────────────────────────────────────────────────────
    @app_commands.command(name="role", description="Everything about a role — permissions, color, members, creation date, position.")
    @app_commands.describe(role="Role to inspect")
    async def role(self, interaction: discord.Interaction, role: discord.Role):
        # All permissions with friendly names
        all_perms = {
            "administrator": "Administrator", "manage_guild": "Manage Server",
            "manage_roles": "Manage Roles", "manage_channels": "Manage Channels",
            "manage_messages": "Manage Messages", "manage_webhooks": "Manage Webhooks",
            "manage_nicknames": "Manage Nicknames", "manage_emojis": "Manage Emojis",
            "kick_members": "Kick Members", "ban_members": "Ban Members",
            "moderate_members": "Timeout Members", "view_audit_log": "View Audit Log",
            "mention_everyone": "Mention Everyone", "send_messages": "Send Messages",
            "embed_links": "Embed Links", "attach_files": "Attach Files",
            "add_reactions": "Add Reactions", "use_external_emojis": "External Emojis",
            "read_message_history": "Read History", "connect": "Connect Voice",
            "speak": "Speak", "move_members": "Move Members",
            "mute_members": "Mute Members", "deafen_members": "Deafen Members",
            "create_instant_invite": "Create Invites",
        }
        has_perms  = [label for perm, label in all_perms.items() if getattr(role.permissions, perm, False)]
        is_admin   = role.permissions.administrator

        embed = discord.Embed(
            title=f"🎭 {role.name}",
            color=role.color if role.color.value else discord.Color.blurple()
        )

        embed.add_field(name="📋 Details", value=(
            f"**ID:** `{role.id}`\n"
            f"**Created:** <t:{int(role.created_at.timestamp())}:D> (<t:{int(role.created_at.timestamp())}:R>)\n"
            f"**Position:** {role.position} (of {len(interaction.guild.roles)})\n"
            f"**Managed:** {'Yes — Bot/Integration' if role.managed else 'No'}"
        ), inline=True)

        embed.add_field(name="🎨 Style", value=(
            f"**Color:** `{role.color}` (#{str(role.color).lstrip('#')})\n"
            f"**Hoisted:** {'Yes — shows separately' if role.hoist else 'No'}\n"
            f"**Mentionable:** {'Yes' if role.mentionable else 'No'}\n"
            f"**Mention:** {role.mention}"
        ), inline=True)

        embed.add_field(name="👥 Members", value=(
            f"**Count:** {len(role.members):,}\n"
            f"**% of Server:** {len(role.members) / max(interaction.guild.member_count, 1) * 100:.1f}%"
        ), inline=True)

        if is_admin:
            embed.add_field(name="🔑 Permissions", value="✅ **ADMINISTRATOR** — Has all permissions", inline=False)
        elif has_perms:
            # Split into two columns
            mid = len(has_perms) // 2 + len(has_perms) % 2
            embed.add_field(name=f"🔑 Permissions ({len(has_perms)})", value="\n".join(f"✅ {p}" for p in has_perms[:mid]), inline=True)
            if has_perms[mid:]:
                embed.add_field(name="\u200b", value="\n".join(f"✅ {p}" for p in has_perms[mid:]), inline=True)
        else:
            embed.add_field(name="🔑 Permissions", value="No special permissions", inline=False)

        # Sample members
        if role.members:
            sample = ", ".join(m.display_name for m in role.members[:8])
            if len(role.members) > 8:
                sample += f" *+{len(role.members)-8} more*"
            embed.add_field(name="👤 Sample Members", value=sample, inline=False)

        embed.set_footer(text=f"Requested by {interaction.user.display_name} | XERO Bot")
        await interaction.response.send_message(embed=embed)

    # ── /info channel ─────────────────────────────────────────────────────
    @app_commands.command(name="channel", description="Full channel breakdown — permissions, settings, topic, slowmode, and more.")
    @app_commands.describe(channel="Channel to inspect (defaults to current)")
    async def channel(self, interaction: discord.Interaction, channel: discord.abc.GuildChannel = None):
        ch = channel or interaction.channel

        embed = discord.Embed(
            title=f"📡 #{ch.name}",
            color=discord.Color.blurple()
        )

        # Channel type
        ch_type_map = {
            discord.TextChannel: "💬 Text Channel",
            discord.VoiceChannel: "🔊 Voice Channel",
            discord.StageChannel: "🎭 Stage Channel",
            discord.ForumChannel: "📋 Forum Channel",
            discord.CategoryChannel: "📁 Category",
        }
        ch_type = next((v for k, v in ch_type_map.items() if isinstance(ch, k)), "Channel")

        embed.add_field(name="📋 Details", value=(
            f"**ID:** `{ch.id}`\n"
            f"**Type:** {ch_type}\n"
            f"**Category:** {ch.category.name if ch.category else 'None'}\n"
            f"**Position:** {ch.position}\n"
            f"**Created:** <t:{int(ch.created_at.timestamp())}:D> (<t:{int(ch.created_at.timestamp())}:R>)"
        ), inline=True)

        if isinstance(ch, discord.TextChannel):
            embed.add_field(name="⚙️ Settings", value=(
                f"**Slowmode:** {ch.slowmode_delay}s\n"
                f"**NSFW:** {'Yes' if ch.is_nsfw() else 'No'}\n"
                f"**News:** {'Yes' if ch.is_news() else 'No'}"
            ), inline=True)
            if ch.topic:
                embed.add_field(name="📝 Topic", value=ch.topic[:500], inline=False)

        elif isinstance(ch, discord.VoiceChannel):
            embed.add_field(name="🔊 Voice Settings", value=(
                f"**Bitrate:** {ch.bitrate // 1000}kbps\n"
                f"**User Limit:** {ch.user_limit or 'Unlimited'}\n"
                f"**Connected:** {len(ch.members)} members"
            ), inline=True)
            if ch.members:
                embed.add_field(name="👥 Connected Members", value=", ".join(m.display_name for m in ch.members[:10]), inline=False)

        # Permission overwrites (non-default)
        overwrites = [(k, v) for k, v in ch.overwrites.items() if k != interaction.guild.default_role]
        if overwrites:
            overwrite_text = []
            for target, ow in overwrites[:6]:
                name = target.name if hasattr(target, 'name') else str(target)
                allows = [p for p, v in ow if v is True]
                denies = [p for p, v in ow if v is False]
                line = f"**{name}:** "
                if allows: line += f"✅ {len(allows)} allows "
                if denies: line += f"❌ {len(denies)} denies"
                overwrite_text.append(line)
            embed.add_field(name=f"🔐 Permission Overwrites ({len(overwrites)})", value="\n".join(overwrite_text), inline=False)

        embed.set_footer(text=f"Requested by {interaction.user.display_name} | XERO Bot")
        await interaction.response.send_message(embed=embed)

    # ── /info bot ─────────────────────────────────────────────────────────
    @app_commands.command(name="bot", description="Detailed XERO bot stats — latency, memory, uptime, server count, command count.")
    async def bot(self, interaction: discord.Interaction):
        uptime_secs = time.time() - self.bot.launch_time
        uptime_str  = f"{int(uptime_secs//86400)}d {int((uptime_secs%86400)//3600)}h {int((uptime_secs%3600)//60)}m {int(uptime_secs%60)}s"
        latency     = round(self.bot.latency * 1000)

        try:
            if HAS_PSUTIL:
                proc   = psutil.Process(os.getpid())
                mem_mb = proc.memory_info().rss / 1024 / 1024
                cpu    = proc.cpu_percent(interval=0.1)
            else:
                mem_mb, cpu = 0.0, 0.0
        except Exception:
            mem_mb, cpu = 0.0, 0.0

        total_commands = 0
        for cog_name, cog in self.bot.cogs.items():
            total_commands += len([c for c in self.bot.tree.get_commands() if True])
        total_commands = len(self.bot.tree.get_commands())

        embed = discord.Embed(
            title="🤖 XERO Bot — System Stats",
            description="Advanced AI-Powered Discord Bot by **Team Flame**\nAll premium features. Completely free.",
            color=discord.Color.blurple()
        )
        embed.set_thumbnail(url=self.bot.user.display_avatar.url)

        embed.add_field(name="⚡ Performance", value=(
            f"**Latency:** {latency}ms {'🟢' if latency < 80 else '🟡' if latency < 150 else '🔴'}\n"
            f"**CPU:** {cpu:.1f}%\n"
            f"**Memory:** {mem_mb:.1f} MB\n"
            f"**Shards:** {self.bot.shard_count or 1}"
        ), inline=True)

        embed.add_field(name="📊 Reach", value=(
            f"**Servers:** {len(self.bot.guilds):,}\n"
            f"**Users:** {sum(g.member_count for g in self.bot.guilds):,}\n"
            f"**Channels:** {sum(len(g.channels) for g in self.bot.guilds):,}\n"
            f"**Slash Commands:** 200+"
        ), inline=True)

        embed.add_field(name="⏱️ Uptime", value=(
            f"**Running:** {uptime_str}\n"
            f"**Started:** <t:{int(self.bot.launch_time)}:R>"
        ), inline=True)

        embed.add_field(name="🛠️ Tech Stack", value=(
            f"**Python:** {platform.python_version()}\n"
            f"**discord.py:** {discord.__version__}\n"
            f"**AI Engine:** NVIDIA Llama 4 Maverick\n"
            f"**Database:** SQLite (aiosqlite)"
        ), inline=True)

        embed.add_field(name="🧩 Cogs Loaded", value=(
            f"**Active:** {len(self.bot.cogs)}\n"
            f"**Commands:** {total_commands}+"
        ), inline=True)

        embed.add_field(name="🌐 Links", value=(
            f"[Invite XERO](https://discord.com/oauth2/authorize?client_id={self.bot.user.id}&permissions=8&scope=bot+applications.commands)\n"
            f"[Support Server](https://discord.gg/nexus)"
        ), inline=True)

        embed.set_footer(text="XERO Bot | Built by Team Flame | Premium Features, Free.")
        await interaction.response.send_message(embed=embed)

    # ── /info emoji ───────────────────────────────────────────────────────
    @app_commands.command(name="emoji", description="Get full details on a custom server emoji — ID, creator, animated, usage tip.")
    @app_commands.describe(emoji_name="Name of the custom emoji (without colons)")
    async def emoji(self, interaction: discord.Interaction, emoji_name: str):
        found = discord.utils.get(interaction.guild.emojis, name=emoji_name)
        if not found:
            return await interaction.response.send_message(embed=error_embed("Not Found", f"No custom emoji named `{emoji_name}` found in this server.\nUse `/info emojis` to see all emojis."), ephemeral=True)
        embed = discord.Embed(
            title=f"{found} :{found.name}:",
            color=discord.Color.blurple()
        )
        embed.set_thumbnail(url=str(found.url))
        embed.add_field(name="📋 Details", value=(
            f"**ID:** `{found.id}`\n"
            f"**Name:** `:{found.name}:`\n"
            f"**Animated:** {'Yes 🎬' if found.animated else 'No'}\n"
            f"**Managed:** {'Yes (Twitch/Integration)' if found.managed else 'No'}\n"
            f"**Created:** <t:{int(found.created_at.timestamp())}:R>"
        ), inline=True)
        embed.add_field(name="🔗 Usage", value=(
            f"**In message:** `<{'a' if found.animated else ''}:{found.name}:{found.id}>`\n"
            f"**Image URL:** [Click here]({found.url})"
        ), inline=True)
        await interaction.response.send_message(embed=embed)

    # ── /info invite ──────────────────────────────────────────────────────
    @app_commands.command(name="invite", description="Look up a Discord invite link and see where it leads.")
    @app_commands.describe(invite_code="Invite code or full URL")
    async def invite(self, interaction: discord.Interaction, invite_code: str):
        await interaction.response.defer(ephemeral=True)
        code = invite_code.split("/")[-1].strip()
        try:
            inv = await self.bot.fetch_invite(code, with_counts=True)
        except discord.NotFound:
            return await interaction.followup.send(embed=error_embed("Invalid Invite", f"The invite `{code}` is invalid or expired."), ephemeral=True)
        except discord.HTTPException as e:
            return await interaction.followup.send(embed=error_embed("Error", str(e)), ephemeral=True)

        embed = comprehensive_embed(
            title=f"🔗 Invite: {code}",
            description=f"Destination: **{inv.guild.name if inv.guild else 'Unknown'}**",
            color=discord.Color.blurple()
        )
        if inv.guild and inv.guild.icon:
            embed.set_thumbnail(url=inv.guild.icon.url)
        embed.add_field(name="🏰 Server", value=(
            f"**Name:** {inv.guild.name if inv.guild else 'Unknown'}\n"
            f"**ID:** `{inv.guild.id if inv.guild else 'Unknown'}`\n"
            f"**Members:** {inv.approximate_member_count:,} online: {inv.approximate_presence_count:,}"
        ), inline=True)
        embed.add_field(name="📡 Channel", value=(
            f"**Name:** #{inv.channel.name if inv.channel else 'Unknown'}\n"
            f"**ID:** `{inv.channel.id if inv.channel else 'Unknown'}`"
        ), inline=True)
        embed.add_field(name="📋 Invite Info", value=(
            f"**Created by:** {inv.inviter or 'Unknown'}\n"
            f"**Uses:** {inv.uses or 0}\n"
            f"**Max Uses:** {inv.max_uses or 'Unlimited'}\n"
            f"**Expires:** {'Never' if not inv.max_age else f'<t:{int((inv.created_at.timestamp() + inv.max_age))}:R>' if inv.created_at else 'Unknown'}"
        ), inline=False)
        await interaction.followup.send(embed=embed)

    # ── /info permissions ─────────────────────────────────────────────────
    @app_commands.command(name="permissions", description="See a complete permission breakdown for any user in any channel.")
    @app_commands.describe(user="User to check (defaults to yourself)", channel="Channel to check permissions in")
    async def permissions(self, interaction: discord.Interaction, user: discord.Member = None, channel: discord.abc.GuildChannel = None):
        target = user or interaction.user
        ch = channel or interaction.channel
        perms = ch.permissions_for(target)

        granted = []
        denied  = []
        perm_labels = {
            "administrator": "Administrator", "manage_guild": "Manage Server",
            "manage_roles": "Manage Roles", "manage_channels": "Manage Channels",
            "manage_messages": "Manage Messages", "manage_webhooks": "Manage Webhooks",
            "manage_nicknames": "Manage Nicknames", "manage_emojis_and_stickers": "Manage Emojis",
            "kick_members": "Kick Members", "ban_members": "Ban Members",
            "moderate_members": "Timeout Members", "view_audit_log": "Audit Log",
            "mention_everyone": "Mention Everyone", "send_messages": "Send Messages",
            "send_messages_in_threads": "Send in Threads", "embed_links": "Embed Links",
            "attach_files": "Attach Files", "add_reactions": "Add Reactions",
            "use_external_emojis": "External Emojis", "read_message_history": "Read History",
            "connect": "Connect Voice", "speak": "Speak", "stream": "Stream",
            "move_members": "Move Members", "mute_members": "Mute Members",
            "deafen_members": "Deafen Members", "create_instant_invite": "Create Invites",
            "view_channel": "View Channel",
        }
        for perm, label in perm_labels.items():
            if getattr(perms, perm, False):
                granted.append(f"✅ {label}")
            else:
                denied.append(f"❌ {label}")

        embed = discord.Embed(
            title=f"🔐 Permissions — {target.display_name} in #{ch.name}",
            color=discord.Color.green() if perms.administrator else discord.Color.blurple()
        )
        embed.set_thumbnail(url=target.display_avatar.url)
        if perms.administrator:
            embed.description = "⚡ **ADMINISTRATOR** — This user has all permissions in this channel."
        else:
            mid = len(granted) // 2 + len(granted) % 2
            embed.add_field(name=f"✅ Granted ({len(granted)})", value="\n".join(granted[:mid]) or "None", inline=True)
            embed.add_field(name="\u200b", value="\n".join(granted[mid:]) or "\u200b", inline=True)
            embed.add_field(name=f"❌ Denied ({len(denied)})", value="\n".join(denied[:10]) or "None", inline=False)
        await interaction.response.send_message(embed=embed)


async def setup(bot: commands.Bot):
    await bot.add_cog(Info(bot))