"""XERO Bot — Server Analytics (7 commands)"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
import aiosqlite
import datetime
from utils.embeds import comprehensive_embed, info_embed, success_embed

logger = logging.getLogger("XERO.Analytics")


class Analytics(commands.GroupCog, name="analytics"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="overview", description="Get a complete analytics overview of your server.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def overview(self, interaction: discord.Interaction):
        await interaction.response.defer()
        guild = interaction.guild
        # Member stats
        total = guild.member_count
        bots = sum(1 for m in guild.members if m.bot) if len(guild.members) < 1000 else 0
        humans = total - bots
        online = guild.member_count  # approximate - members cache not reliable on hosted bots
        # Channel stats
        text_ch = len([c for c in guild.channels if isinstance(c, discord.TextChannel)])
        voice_ch = len([c for c in guild.channels if isinstance(c, discord.VoiceChannel)])
        # Economy stats
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT COUNT(*), SUM(wallet+bank), AVG(wallet+bank) FROM economy WHERE guild_id=?", (interaction.guild.id,)) as c:
                eco = await c.fetchone()
            async with db.execute("SELECT COUNT(*), SUM(total_xp), MAX(level) FROM levels WHERE guild_id=?", (interaction.guild.id,)) as c:
                lvl = await c.fetchone()
            async with db.execute("SELECT SUM(commands_used), SUM(messages_sent) FROM user_stats WHERE guild_id=?", (interaction.guild.id,)) as c:
                stats = await c.fetchone()
            async with db.execute("SELECT COUNT(*) FROM mod_cases WHERE guild_id=?", (interaction.guild.id,)) as c:
                mod_count = (await c.fetchone())[0]
            async with db.execute("SELECT COUNT(*) FROM warnings WHERE guild_id=?", (interaction.guild.id,)) as c:
                warn_count = (await c.fetchone())[0]
        embed = comprehensive_embed(
            title=f"📊 {guild.name} — Analytics Overview",
            description=f"Comprehensive insights for your server",
            color=discord.Color.blurple(),
            thumbnail_url=guild.icon.url if guild.icon else None
        )
        embed.add_field(name="👥 Members", value=(
            f"**Total:** {total:,}\n"
            f"**Humans:** {humans:,} | **Bots:** {bots:,}\n"
            f"**Online Now:** {online:,} ({int(online/max(total,1)*100)}%)"
        ), inline=True)
        embed.add_field(name="📡 Structure", value=(
            f"**Text Channels:** {text_ch}\n"
            f"**Voice Channels:** {voice_ch}\n"
            f"**Roles:** {len(guild.roles)-1}"
        ), inline=True)
        embed.add_field(name="💬 Activity", value=(
            f"**Commands Used:** {(stats[0] or 0):,}\n"
            f"**Messages Tracked:** {(stats[1] or 0):,}"
        ), inline=True)
        if eco and eco[0]:
            embed.add_field(name="💰 Economy", value=(
                f"**Active Users:** {eco[0]:,}\n"
                f"**Total Wealth:** ${int(eco[1] or 0):,}\n"
                f"**Avg Net Worth:** ${int(eco[2] or 0):,}"
            ), inline=True)
        if lvl and lvl[0]:
            embed.add_field(name="📈 Leveling", value=(
                f"**Ranked Members:** {lvl[0]:,}\n"
                f"**Total XP Earned:** {int(lvl[1] or 0):,}\n"
                f"**Highest Level:** {lvl[2] or 0}"
            ), inline=True)
        embed.add_field(name="⚖️ Moderation", value=(
            f"**Total Cases:** {mod_count:,}\n"
            f"**Total Warnings:** {warn_count:,}"
        ), inline=True)
        # AI insight
        try:
            ai_prompt = (
                f"Give a 2-sentence sharp insight about this Discord server's health and activity:\n"
                f"Members: {total:,} ({online:,} online, {bots} bots)\n"
                f"Commands used: {(stats[0] or 0):,}, Messages: {(stats[1] or 0):,}\n"
                f"Mod cases: {mod_count}, Warnings: {warn_count}\n"
                f"Economy active users: {eco[0] if eco else 0}, XP ranked: {lvl[0] if lvl else 0}\n"
                f"Be direct, insightful, specific. No fluff."
            )
            ai_insight = await self.bot.nvidia.ask(ai_prompt)
            if ai_insight:
                embed.add_field(name="🤖 AI Insight", value=ai_insight[:400], inline=False)
        except Exception:
            pass
        embed.set_footer(text=f"XERO Analytics  •  AI-Powered  •  {datetime.datetime.now().strftime('%Y-%m-%d %H:%M')}")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="top-members", description="See the most active members by commands and messages.")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def top_members(self, interaction: discord.Interaction):
        await interaction.response.defer()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT user_id, commands_used, messages_sent FROM user_stats WHERE guild_id=? ORDER BY commands_used+messages_sent DESC LIMIT 10",
                (interaction.guild.id,)
            ) as c:
                rows = [dict(r) for r in await c.fetchall()]
        if not rows:
            return await interaction.followup.send(embed=info_embed("No Data", "No activity data yet."))
        embed = comprehensive_embed(title="🏆 Most Active Members", color=discord.Color.gold())
        medals = ["🥇","🥈","🥉"] + [f"**#{i}**" for i in range(4, 11)]
        lines = []
        for i, row in enumerate(rows):
            member = interaction.guild.get_member(row["user_id"])
            name = member.display_name if member else f"User {row['user_id']}"
            lines.append(f"{medals[i]} **{name}** — {row['commands_used']:,} cmds | {row['messages_sent']:,} msgs")
        embed.description = "\n".join(lines)
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="economy-stats", description="Detailed economy analytics for the server.")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def economy_stats(self, interaction: discord.Interaction):
        await interaction.response.defer()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT COUNT(*) as users, SUM(wallet) as total_wallet, SUM(bank) as total_bank, "
                "SUM(total_earned) as earned, SUM(total_spent) as spent, "
                "MAX(wallet+bank) as richest, MIN(wallet+bank) as poorest, AVG(wallet+bank) as avg "
                "FROM economy WHERE guild_id=?",
                (interaction.guild.id,)
            ) as c:
                stats = dict(await c.fetchone())
            async with db.execute(
                "SELECT COUNT(*) FROM economy_shop WHERE guild_id=?", (interaction.guild.id,)
            ) as c:
                shop_items = (await c.fetchone())[0]
            async with db.execute(
                "SELECT COUNT(*) FROM economy_inventory WHERE guild_id=?", (interaction.guild.id,)
            ) as c:
                purchases = (await c.fetchone())[0]
        if not stats["users"]:
            return await interaction.followup.send(embed=info_embed("No Economy Data", "No economy activity yet."))
        embed = comprehensive_embed(title="💰 Economy Analytics", description=f"**{stats['users']:,}** active economy users", color=discord.Color.gold())
        embed.add_field(name="💵 Wealth Distribution", value=(
            f"**Total in Wallets:** ${int(stats['total_wallet'] or 0):,}\n"
            f"**Total in Banks:** ${int(stats['total_bank'] or 0):,}\n"
            f"**Combined Economy:** ${int((stats['total_wallet'] or 0)+(stats['total_bank'] or 0)):,}"
        ), inline=True)
        embed.add_field(name="📊 Averages", value=(
            f"**Avg Net Worth:** ${int(stats['avg'] or 0):,}\n"
            f"**Richest:** ${int(stats['richest'] or 0):,}\n"
            f"**Poorest:** ${int(stats['poorest'] or 0):,}"
        ), inline=True)
        embed.add_field(name="🔄 Flow", value=(
            f"**Total Earned:** ${int(stats['earned'] or 0):,}\n"
            f"**Total Spent:** ${int(stats['spent'] or 0):,}\n"
            f"**Shop Items:** {shop_items:,} | **Purchases:** {purchases:,}"
        ), inline=True)
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="moderation-stats", description="Detailed moderation statistics and trends.")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def moderation_stats(self, interaction: discord.Interaction):
        await interaction.response.defer()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT action, COUNT(*) as count FROM mod_cases WHERE guild_id=? GROUP BY action ORDER BY count DESC",
                (interaction.guild.id,)
            ) as c:
                action_breakdown = [dict(r) for r in await c.fetchall()]
            async with db.execute(
                "SELECT COUNT(*) FROM mod_cases WHERE guild_id=? AND timestamp >= datetime('now', '-30 days')",
                (interaction.guild.id,)
            ) as c:
                last_30 = (await c.fetchone())[0]
            async with db.execute(
                "SELECT COUNT(*) FROM mod_cases WHERE guild_id=? AND timestamp >= datetime('now', '-7 days')",
                (interaction.guild.id,)
            ) as c:
                last_7 = (await c.fetchone())[0]
            async with db.execute(
                "SELECT user_id, COUNT(*) as total FROM mod_cases WHERE guild_id=? GROUP BY user_id ORDER BY total DESC LIMIT 5",
                (interaction.guild.id,)
            ) as c:
                most_actioned = [dict(r) for r in await c.fetchall()]
        embed = comprehensive_embed(title="⚖️ Moderation Analytics", color=discord.Color.orange())
        embed.add_field(name="📅 Timeline", value=(
            f"**Last 7 days:** {last_7:,} actions\n"
            f"**Last 30 days:** {last_30:,} actions"
        ), inline=True)
        if action_breakdown:
            breakdown_text = "\n".join([f"**{r['action'].capitalize()}:** {r['count']:,}" for r in action_breakdown])
            embed.add_field(name="📊 By Action", value=breakdown_text, inline=True)
        if most_actioned:
            actioned_lines = []
            for row in most_actioned:
                member = interaction.guild.get_member(row["user_id"])
                name = member.display_name if member else f"User {row['user_id']}"
                actioned_lines.append(f"**{name}:** {row['total']} times")
            embed.add_field(name="🔴 Most Actioned Users", value="\n".join(actioned_lines), inline=False)
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="level-stats", description="Detailed leveling and XP analytics.")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def level_stats(self, interaction: discord.Interaction):
        await interaction.response.defer()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT COUNT(*) as users, SUM(total_xp) as total_xp, AVG(total_xp) as avg_xp, "
                "MAX(level) as max_level, AVG(level) as avg_level, "
                "SUM(CASE WHEN level >= 10 THEN 1 ELSE 0 END) as level10plus, "
                "SUM(CASE WHEN level >= 25 THEN 1 ELSE 0 END) as level25plus "
                "FROM levels WHERE guild_id=?",
                (interaction.guild.id,)
            ) as c:
                stats = dict(await c.fetchone())
        if not stats["users"]:
            return await interaction.followup.send(embed=info_embed("No Level Data", "No leveling data yet."))
        embed = comprehensive_embed(title="📊 Leveling Analytics", color=discord.Color.purple())
        embed.add_field(name="👥 Users", value=f"**Ranked:** {stats['users']:,}", inline=True)
        embed.add_field(name="⭐ XP", value=(
            f"**Total Earned:** {int(stats['total_xp'] or 0):,}\n"
            f"**Average:** {int(stats['avg_xp'] or 0):,}"
        ), inline=True)
        embed.add_field(name="📈 Levels", value=(
            f"**Highest Level:** {stats['max_level'] or 0}\n"
            f"**Average Level:** {int(stats['avg_level'] or 0)}\n"
            f"**Level 10+:** {stats['level10plus']:,}\n"
            f"**Level 25+:** {stats['level25plus']:,}"
        ), inline=True)
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="member-growth", description="View member join/leave trends (today vs all time).")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def member_growth(self, interaction: discord.Interaction):
        await interaction.response.defer()
        guild = interaction.guild
        now = discord.utils.utcnow()
        # Analyze join dates from cached members
        joined_today = sum(1 for m in guild.members if (now - m.joined_at).days < 1)
        joined_week = sum(1 for m in guild.members if (now - m.joined_at).days < 7)
        joined_month = sum(1 for m in guild.members if (now - m.joined_at).days < 30)
        # Account ages
        new_accounts = sum(1 for m in guild.members if not m.bot and (now - m.created_at).days < 30)
        old_accounts = sum(1 for m in guild.members if not m.bot and (now - m.created_at).days > 365)
        embed = comprehensive_embed(title="📈 Member Growth Analytics", color=discord.Color.green())
        embed.add_field(name="📅 Recent Joins", value=(
            f"**Today:** {joined_today:,}\n"
            f"**This Week:** {joined_week:,}\n"
            f"**This Month:** {joined_month:,}\n"
            f"**All Time:** {guild.member_count:,}"
        ), inline=True)
        embed.add_field(name="👤 Account Ages", value=(
            f"**New (<30 days):** {new_accounts:,}\n"
            f"**Veteran (1+ year):** {old_accounts:,}\n"
            f"**Server Created:** <t:{int(guild.created_at.timestamp())}:R>"
        ), inline=True)
        embed.add_field(name="⭐ Boost Status", value=(
            f"**Level:** {guild.premium_tier}\n"
            f"**Boosts:** {guild.premium_subscription_count}\n"
            f"**Boosters:** {len(guild.premium_subscribers):,}"
        ), inline=True)
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="channel-activity", description="See which channels are most active.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def channel_activity(self, interaction: discord.Interaction):
        await interaction.response.defer()
        # Check recent messages per channel (scan last 100 in each visible channel)
        channel_counts = {}
        now = discord.utils.utcnow()
        for ch in interaction.guild.text_channels[:20]:
            if not ch.permissions_for(interaction.guild.me).read_message_history:
                continue
            try:
                count = 0
                async for msg in ch.history(limit=200, after=now - datetime.timedelta(days=7)):
                    if not msg.author.bot:
                        count += 1
                if count > 0:
                    channel_counts[ch] = count
            except Exception:
                pass
        if not channel_counts:
            return await interaction.followup.send(embed=info_embed("No Data", "Could not read channel history."))
        sorted_channels = sorted(channel_counts.items(), key=lambda x: x[1], reverse=True)
        embed = comprehensive_embed(title="📡 Channel Activity (Last 7 Days)", description="Human messages per channel", color=discord.Color.blurple())
        for ch, count in sorted_channels[:10]:
            bar = "█" * min(int(count / max(sorted_channels[0][1], 1) * 15), 15)
            embed.add_field(name=f"#{ch.name}", value=f"`{bar}` **{count:,}** messages", inline=False)
        await interaction.followup.send(embed=embed)


    @app_commands.command(name="peak-hours", description="Analyze when this server is most active.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def peak_hours(self, interaction: discord.Interaction):
        await interaction.response.defer()
        # Scan recent messages across channels to find peak hours
        hour_counts = {h: 0 for h in range(24)}
        now = discord.utils.utcnow()
        scanned = 0
        for ch in interaction.guild.text_channels[:10]:
            if not ch.permissions_for(interaction.guild.me).read_message_history: continue
            try:
                async for msg in ch.history(limit=500, after=now - datetime.timedelta(days=14)):
                    if not msg.author.bot:
                        hour_counts[msg.created_at.hour] += 1
                        scanned += 1
            except Exception: pass
        if scanned == 0:
            return await interaction.followup.send(embed=info_embed("No Data","Couldn't read message history."))
        peak_hour = max(hour_counts, key=hour_counts.get)
        sorted_hours = sorted(hour_counts.items(), key=lambda x: x[1], reverse=True)
        top5 = sorted_hours[:5]
        bar_lines = []
        max_count = sorted_hours[0][1] or 1
        for h, count in sorted(hour_counts.items()):
            bar = "█" * int(count / max_count * 12)
            active = " ◄ PEAK" if h == peak_hour else ""
            bar_lines.append(f"`{h:02d}:00` {bar or '░'} {count}{active}")
        embed = comprehensive_embed(title=f"⏰  Peak Hours — {interaction.guild.name}", color=0x00D4FF)
        mid = len(bar_lines) // 2
        embed.add_field(name="🌅 00:00–11:59", value="\n".join(bar_lines[:12]), inline=True)
        embed.add_field(name="🌇 12:00–23:59", value="\n".join(bar_lines[12:]), inline=True)
        embed.add_field(name="🏆 Peak Time",   value=f"**{peak_hour:02d}:00 UTC** with {hour_counts[peak_hour]:,} messages", inline=False)
        # AI analysis
        try:
            top_str = ", ".join(f"{h:02d}:00 ({c} msgs)" for h,c in top5)
            ai = await self.bot.nvidia.ask(f"Discord server peak activity hours (UTC): {top_str}. Give one brief insight about what this suggests about the community (timezone, demographics, etc.). 2 sentences max.")
            if ai: embed.add_field(name="🤖 AI Insight", value=ai, inline=False)
        except Exception: pass
        embed.set_footer(text=f"Based on {scanned:,} messages (last 14 days)  •  XERO Analytics")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="server-health", description="AI-generated server health score and recommendations.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def server_health(self, interaction: discord.Interaction):
        await interaction.response.defer()
        guild = interaction.guild
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT SUM(commands_used),SUM(messages_sent) FROM user_stats WHERE guild_id=?", (guild.id,)) as c:
                stats = await c.fetchone()
            async with db.execute("SELECT COUNT(*) FROM mod_cases WHERE guild_id=? AND timestamp >= datetime(\'now\', \'-7 days\')", (guild.id,)) as c:
                cases_7d = (await c.fetchone())[0]
        online = sum(1 for m in guild.members if m.status != discord.Status.offline and not m.bot)
        humans = guild.member_count - sum(1 for m in guild.members if m.bot)
        engagement = min(100, int((stats[1] or 0) / max(humans, 1) * 10))
        bot_ratio  = sum(1 for m in guild.members if m.bot) / max(guild.member_count, 1) * 100
        online_pct = online / max(humans, 1) * 100
        prompt = (
            f"Rate this Discord server's health (0-100) and give 3 specific recommendations:\n"
            f"Members: {guild.member_count:,} ({humans:,} humans, {online:,} online = {online_pct:.0f}%)\n"
            f"Bot ratio: {bot_ratio:.0f}%  |  Boost level: {guild.premium_tier}\n"
            f"Messages tracked: {stats[1] or 0:,}  |  Commands used: {stats[0] or 0:,}\n"
            f"Mod actions (7d): {cases_7d}  |  Roles: {len(guild.roles)-1}  |  Channels: {len(guild.text_channels)}\n"
            f"Format:\nSCORE: [0-100]\nRECOMMENDATION 1: [specific action]\nRECOMMENDATION 2: [specific action]\nRECOMMENDATION 3: [specific action]"
        )
        try:
            result = await self.bot.nvidia.ask(prompt)
            lines  = result.strip().split('\n')
            score_line = next((l.replace('SCORE:','').strip() for l in lines if 'SCORE:' in l), "70")
            health_score = max(0, min(100, int(''.join(c for c in score_line if c.isdigit())[:3] or "70")))
            recs = [l.replace('RECOMMENDATION 1:','').replace('RECOMMENDATION 2:','').replace('RECOMMENDATION 3:','').strip() 
                    for l in lines if 'RECOMMENDATION' in l]
        except Exception:
            health_score = 70; recs = ["Increase member engagement with events","Set up auto-moderation","Configure welcome messages"]
        color = 0x00FF94 if health_score >= 75 else 0xFFB800 if health_score >= 50 else 0xFF3B5C
        bar   = "█" * (health_score//10) + "░" * (10 - health_score//10)
        embed = comprehensive_embed(title=f"❤️  Server Health — {guild.name}", color=color)
        embed.add_field(name="💊 Health Score", value=f"**{health_score}/100**\n`{bar}`", inline=True)
        embed.add_field(name="👥 Online Rate",  value=f"{online_pct:.0f}%",               inline=True)
        embed.add_field(name="💎 Boost Level",  value=f"Level {guild.premium_tier}",       inline=True)
        if recs:
            embed.add_field(name="🎯 AI Recommendations", value="\n".join(f"• {r}" for r in recs[:3]), inline=False)
        embed.set_footer(text="XERO Analytics  •  AI-Powered by Nemotron")
        await interaction.followup.send(embed=embed)

async def setup(bot):
    await bot.add_cog(Analytics(bot))
