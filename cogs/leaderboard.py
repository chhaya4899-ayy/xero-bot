"""XERO Bot — Leaderboards (3 commands) — XP, Economy, Activity"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
from utils.embeds import comprehensive_embed, info_embed, XERO, FOOTER_LEVEL, FOOTER_ECO, FOOTER_MAIN

logger = logging.getLogger("XERO.Leaderboard")

MEDALS = ["🥇", "🥈", "🥉"] + [f"`#{i}`" for i in range(4, 16)]


class Leaderboard(commands.GroupCog, name="leaderboard"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="xp", description="Server XP leaderboard — levels, total XP, and multipliers for the top 15.")
    @command_guard
    async def xp(self, interaction: discord.Interaction):
        await interaction.response.defer()
        lb = await self.bot.db.get_level_leaderboard(interaction.guild.id, 15)
        if not lb:
            return await interaction.followup.send(embed=info_embed(
                "No XP Data Yet",
                "Nobody has earned XP yet!\n\n"
                "Members earn XP by:\n"
                "• **Messaging** — 15-25 XP every 60s\n"
                "• **Using bot commands** — 2× XP bonus\n"
                "• **Leveling up** — multipliers increase"
            ))

        embed = discord.Embed(
            title="📊  XP Leaderboard",
            description=f"Top {len(lb)} members in **{interaction.guild.name}**",
            color=XERO.LEVEL
        )
        if interaction.guild.icon:
            embed.set_thumbnail(url=interaction.guild.icon.url)

        lines = []
        for i, row in enumerate(lb):
            member = interaction.guild.get_member(row["user_id"])
            name   = member.display_name if member else f"User {row['user_id']}"
            level  = row["level"]
            txp    = row["total_xp"]
            # Show multiplier for this level
            passive = min(1.0 + max(0, level-1)*0.05, 3.0)
            mult_str = f"{passive:.1f}×" if passive > 1.0 else "1.0×"
            lines.append(
                f"{MEDALS[i]} **{name}**\n"
                f"　Level **{level}** · {txp:,} XP · {mult_str} mult"
            )

        # Split into two fields for readability
        mid = len(lines)//2 + len(lines)%2
        embed.add_field(name="🏆 Top Ranked", value="\n".join(lines[:mid]) or "—", inline=True)
        if lines[mid:]:
            embed.add_field(name="\u200b", value="\n".join(lines[mid:]), inline=True)

        # Caller's own rank
        caller_pos = next((i+1 for i,r in enumerate(lb) if r["user_id"]==interaction.user.id), None)
        if caller_pos:
            embed.add_field(name="📍 Your Position", value=f"**#{caller_pos}** on this leaderboard", inline=False)
        else:
            all_lb = await self.bot.db.get_level_leaderboard(interaction.guild.id, 1000)
            caller_pos = next((i+1 for i,r in enumerate(all_lb) if r["user_id"]==interaction.user.id), None)
            if caller_pos:
                embed.add_field(name="📍 Your Position", value=f"**#{caller_pos}** overall — keep chatting to climb!", inline=False)

        embed.set_footer(text=f"XERO Levels  •  Earn XP by chatting + using commands")
        from utils.embeds import brand_embed
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        if file:
            await interaction.followup.send(embed=embed, file=file)
        else:
            await interaction.followup.send(embed=embed)

    @app_commands.command(name="economy", description="Server wealth leaderboard — wallet, bank, net worth for the top 15 richest members.")
    @command_guard
    async def economy(self, interaction: discord.Interaction):
        await interaction.response.defer()
        lb = await self.bot.db.get_economy_leaderboard(interaction.guild.id, 15)
        if not lb:
            return await interaction.followup.send(embed=info_embed(
                "No Economy Data Yet",
                "Nobody has earned money yet!\n\n"
                "Ways to earn:\n"
                "• `/economy work` — every hour\n"
                "• `/daily` — with streak multipliers\n"
                "• `/economy slots`, `/economy blackjack`\n"
                "• `/heist` — group robbery"
            ))

        embed = discord.Embed(
            title="💰  Wealth Leaderboard",
            description=f"Top {len(lb)} richest members in **{interaction.guild.name}**",
            color=XERO.GOLD
        )
        if interaction.guild.icon:
            embed.set_thumbnail(url=interaction.guild.icon.url)

        lines = []
        for i, row in enumerate(lb):
            member = interaction.guild.get_member(row["user_id"])
            name   = member.display_name if member else f"User {row['user_id']}"
            total  = row["total"]
            wallet = row.get("wallet", 0)
            bank   = row.get("bank", 0)
            lines.append(
                f"{MEDALS[i]} **{name}**\n"
                f"　**${total:,}** net worth · 👛 ${wallet:,} · 🏦 ${bank:,}"
            )

        mid = len(lines)//2 + len(lines)%2
        embed.add_field(name="💎 Top Earners", value="\n".join(lines[:mid]) or "—", inline=True)
        if lines[mid:]:
            embed.add_field(name="\u200b", value="\n".join(lines[mid:]), inline=True)

        # Caller's stats
        caller_eco = await self.bot.db.get_economy(interaction.user.id, interaction.guild.id)
        caller_pos = next((i+1 for i,r in enumerate(lb) if r["user_id"]==interaction.user.id), None)
        caller_net = caller_eco["wallet"] + caller_eco["bank"]
        if caller_pos:
            embed.add_field(name="📍 Your Wealth", value=f"**#{caller_pos}** — ${caller_net:,} net worth", inline=False)
        else:
            all_lb = await self.bot.db.get_economy_leaderboard(interaction.guild.id, 500)
            caller_pos = next((i+1 for i,r in enumerate(all_lb) if r["user_id"]==interaction.user.id), None)
            rank_str = f"**#{caller_pos}**" if caller_pos else "Unranked"
            embed.add_field(name="📍 Your Wealth", value=f"{rank_str} — ${caller_net:,} net worth", inline=False)

        embed.set_footer(text="XERO Economy  •  Net worth = wallet + bank")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="commands", description="Most active members leaderboard — commands used and messages sent.")
    @command_guard
    async def commands_lb(self, interaction: discord.Interaction):
        await interaction.response.defer()
        lb = await self.bot.db.get_stats_leaderboard(interaction.guild.id, 15)
        if not lb:
            return await interaction.followup.send(embed=info_embed(
                "No Activity Data Yet",
                "No command usage tracked yet. Start using XERO commands to appear here!"
            ))

        embed = discord.Embed(
            title="🔥  Most Active Members",
            description=f"Top {len(lb)} by commands used in **{interaction.guild.name}**",
            color=XERO.PRIMARY
        )
        if interaction.guild.icon:
            embed.set_thumbnail(url=interaction.guild.icon.url)

        lines = []
        for i, row in enumerate(lb):
            member = interaction.guild.get_member(row["user_id"])
            name   = member.display_name if member else f"User {row['user_id']}"
            cmds   = row["commands_used"]
            msgs   = row["messages_sent"]
            lines.append(
                f"{MEDALS[i]} **{name}**\n"
                f"　⚡ {cmds:,} commands · 💬 {msgs:,} messages"
            )

        mid = len(lines)//2 + len(lines)%2
        embed.add_field(name="🏆 Power Users", value="\n".join(lines[:mid]) or "—", inline=True)
        if lines[mid:]:
            embed.add_field(name="\u200b", value="\n".join(lines[mid:]), inline=True)

        # Caller's stats
        caller_stats = await self.bot.db.get_user_stats(interaction.user.id, interaction.guild.id)
        caller_pos   = next((i+1 for i,r in enumerate(lb) if r["user_id"]==interaction.user.id), None)
        if caller_pos:
            embed.add_field(name="📍 Your Stats", value=f"**#{caller_pos}** — {caller_stats.get('commands_used',0):,} commands · {caller_stats.get('messages_sent',0):,} messages", inline=False)
        else:
            embed.add_field(name="📍 Your Stats", value=f"Unranked — {caller_stats.get('commands_used',0):,} commands · {caller_stats.get('messages_sent',0):,} messages", inline=False)

        embed.set_footer(text="XERO Bot  •  Every command & message you send is tracked")
        await interaction.followup.send(embed=embed)


async def setup(bot):
    await bot.add_cog(Leaderboard(bot))
