"""XERO Bot — Levels & XP System (8 commands)"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, level_embed, comprehensive_embed

logger = logging.getLogger("XERO.Levels")


class Levels(commands.GroupCog, name="levels"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="rank", description="View your level, XP progress bar, server rank, multiplier, and next reward.")
    @app_commands.describe(user="User to check (default: yourself)")
    @command_guard
    async def rank(self, interaction: discord.Interaction, user: discord.Member = None):
        await interaction.response.defer()
        target   = user or interaction.user
        data     = await self.bot.db.get_level(target.id, interaction.guild.id)
        lb       = await self.bot.db.get_level_leaderboard(interaction.guild.id, limit=500)
        rank     = next((i + 1 for i, r in enumerate(lb) if r["user_id"] == target.id), len(lb) + 1)
        level    = data["level"]
        xp       = data["xp"]
        total_xp = data["total_xp"]
        # Use EXACT same formula as database.py xp_for_level
        next_xp  = int(100 * (level + 1) ** 2.2)
        # XP multiplier info
        passive  = min(1.0 + max(0, level - 1) * 0.05, 3.0)
        cmd_mult = passive + 1.0
        # Next level reward
        rewards  = await self.bot.db.get_level_rewards(interaction.guild.id)
        next_reward = next((r for r in sorted(rewards, key=lambda x: x["level"]) if r["level"] > level), None)

        from utils.embeds import brand_embed, comprehensive_embed
        embed = level_embed(target, level, xp, next_xp, total_xp, rank)
        embed.add_field(name="⚡ XP Multipliers", value=f"Messaging: **{passive:.2f}×**\nBot commands: **{cmd_mult:.2f}×**", inline=True)
        embed.add_field(name="📊 Server Rank", value=f"**#{rank}** of {len(lb)} ranked", inline=True)
        if next_reward:
            role = interaction.guild.get_role(next_reward["role_id"])
            if role:
                xp_gap = sum(int(100*(l+1)**2.2) for l in range(level, next_reward["level"]))
                embed.add_field(name="🎁 Next Reward", value=f"{role.mention} at **Level {next_reward['level']}**\n~{xp_gap:,} XP away", inline=True)
        
        # Unified Branding
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        if file:
            await interaction.followup.send(embed=embed, file=file)
        else:
            await interaction.followup.send(embed=embed)

    @app_commands.command(name="leaderboard", description="View the server XP leaderboard.")
    async def leaderboard(self, interaction: discord.Interaction):
        lb = await self.bot.db.get_level_leaderboard(interaction.guild.id, 10)
        if not lb:
            return await interaction.response.send_message(embed=info_embed("Empty", "No level data yet. Start chatting to earn XP!"))
        from utils.embeds import brand_embed, comprehensive_embed
        embed = comprehensive_embed(title="📊 XP Leaderboard", description="Top 10 members by total XP", color=discord.Color.purple())
        medals = ["🥇", "🥈", "🥉"] + [f"**#{i}**" for i in range(4, 11)]
        for i, row in enumerate(lb):
            user = interaction.guild.get_member(row["user_id"])
            name = user.display_name if user else f"User {row['user_id']}"
            embed.add_field(name=f"{medals[i]} {name}", value=f"Level **{row['level']}** — {row['total_xp']:,} XP", inline=True)
        
        # Unified Branding
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        if file:
            await interaction.response.send_message(embed=embed, file=file)
        else:
            await interaction.response.send_message(embed=embed)

    @app_commands.command(name="set-xp", description="[Admin] Set a user's XP and level.")
    @app_commands.describe(user="User to modify", xp="XP amount", level="Level to set")
    @app_commands.checks.has_permissions(administrator=True)
    async def set_xp(self, interaction: discord.Interaction, user: discord.Member, xp: int, level: int):
        xp = max(0, xp)
        level = max(0, level)
        await self.bot.db.set_user_xp(user.id, interaction.guild.id, xp, level)
        await interaction.response.send_message(embed=success_embed("XP Updated", f"{user.mention} is now **Level {level}** with **{xp:,} XP**."))

    @app_commands.command(name="add-xp", description="[Admin] Add XP to a user.")
    @app_commands.describe(user="User to give XP", amount="Amount of XP to add")
    @app_commands.checks.has_permissions(administrator=True)
    async def add_xp(self, interaction: discord.Interaction, user: discord.Member, amount: int):
        leveled_up, new_level = await self.bot.db.update_xp(user.id, interaction.guild.id, max(1, amount))
        msg = f"Added **{amount:,} XP** to {user.mention}."
        if leveled_up:
            msg += f"\n🎉 They leveled up to **Level {new_level}**!"
        await interaction.response.send_message(embed=success_embed("XP Added", msg))

    @app_commands.command(name="reset", description="[Admin] Reset a user's XP and level to zero.")
    @app_commands.describe(user="User to reset")
    @app_commands.checks.has_permissions(administrator=True)
    async def reset(self, interaction: discord.Interaction, user: discord.Member):
        await self.bot.db.set_user_xp(user.id, interaction.guild.id, 0, 0)
        await interaction.response.send_message(embed=success_embed("XP Reset", f"{user.mention}'s XP and level have been reset to 0."))

    @app_commands.command(name="reward-add", description="[Admin] Add a role reward for reaching a level.")
    @app_commands.describe(level="Level required to earn the reward", role="Role to grant")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def reward_add(self, interaction: discord.Interaction, level: int, role: discord.Role):
        await self.bot.db.add_level_reward(interaction.guild.id, level, role.id)
        await interaction.response.send_message(embed=success_embed("Level Reward Added", f"Members will receive {role.mention} when they reach **Level {level}**."))

    @app_commands.command(name="reward-remove", description="[Admin] Remove a level reward.")
    @app_commands.describe(level="Level whose reward to remove")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def reward_remove(self, interaction: discord.Interaction, level: int):
        await self.bot.db.remove_level_reward(interaction.guild.id, level)
        await interaction.response.send_message(embed=success_embed("Reward Removed", f"Level **{level}** reward has been removed."))

    @app_commands.command(name="rewards", description="View all level-up role rewards for this server.")
    async def rewards(self, interaction: discord.Interaction):
        rewards = await self.bot.db.get_level_rewards(interaction.guild.id)
        if not rewards:
            return await interaction.response.send_message(embed=info_embed("No Rewards", "No level rewards configured. Admins can add them with `/levels reward-add`."))
        from utils.embeds import brand_embed, comprehensive_embed
        embed = comprehensive_embed(title="🎁 Level Rewards", description="Earn these roles by leveling up!", color=discord.Color.purple())
        for r in rewards:
            role = interaction.guild.get_role(r["role_id"])
            role_mention = role.mention if role else f"Deleted Role ({r['role_id']})"
            embed.add_field(name=f"Level {r['level']}", value=role_mention, inline=True)
            
        # Unified Branding
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        if file:
            await interaction.response.send_message(embed=embed, file=file)
        else:
            await interaction.response.send_message(embed=embed)


    @app_commands.command(name="voice-xp", description="Configure voice XP — earn XP while in voice channels.")
    @app_commands.describe(enabled="Enable or disable voice XP",xp_per_minute="XP earned per minute in voice (default 5)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def voice_xp(self, interaction: discord.Interaction, enabled: bool, xp_per_minute: int = 5):
        await self.bot.db.update_guild_setting(interaction.guild.id, "voice_xp_enabled", 1 if enabled else 0)
        await self.bot.db.update_guild_setting(interaction.guild.id, "voice_xp_rate", max(1,min(50,xp_per_minute)))
        if enabled:
            await interaction.response.send_message(embed=success_embed("Voice XP Enabled",
                "Members earn **" + str(xp_per_minute) + " XP/minute** while in voice channels.\n"
                "*AFK channels and channels with only 1 person don't count.*"
            ))
        else:
            await interaction.response.send_message(embed=success_embed("Voice XP Disabled","Voice channels no longer grant XP."))

    @app_commands.command(name="role-multiplier", description="Give a role a custom XP multiplier. E.g. boosters get 2x XP.")
    @app_commands.describe(role="Role to configure",multiplier="XP multiplier (1.0=normal, 2.0=double, 0=remove)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def role_multiplier(self, interaction: discord.Interaction, role: discord.Role, multiplier: float):
        import aiosqlite
        multiplier = max(0.0, min(5.0, multiplier))
        async with self.bot.db._db_context() as db:
            await db.execute("CREATE TABLE IF NOT EXISTS xp_role_multipliers (guild_id INTEGER,role_id INTEGER,multiplier REAL,PRIMARY KEY(guild_id,role_id))")
            if multiplier == 0:
                await db.execute("DELETE FROM xp_role_multipliers WHERE guild_id=? AND role_id=?",(interaction.guild.id,role.id))
                await db.commit()
                return await interaction.response.send_message(embed=success_embed("Multiplier Removed",role.mention + " no longer has an XP multiplier."))
            await db.execute("INSERT OR REPLACE INTO xp_role_multipliers (guild_id,role_id,multiplier) VALUES (?,?,?)",(interaction.guild.id,role.id,multiplier))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Multiplier Set",role.mention + " now gives **" + str(multiplier) + "x XP** to members with this role."))

    @app_commands.command(name="levelup-dm", description="Configure level-up DM — bot DMs members when they level up.")
    @app_commands.describe(enabled="Enable or disable",message="Custom message ({user} {level} {server})")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def levelup_dm(self, interaction: discord.Interaction, enabled: bool, message: str = ""):
        await self.bot.db.update_guild_setting(interaction.guild.id, "levelup_dm_enabled", 1 if enabled else 0)
        if message:
            await self.bot.db.update_guild_setting(interaction.guild.id, "levelup_dm_message", message)
        if enabled:
            preview = (message or "Congrats {user}! You reached Level {level} in {server}!").replace("{user}",interaction.user.display_name).replace("{level}","10").replace("{server}",interaction.guild.name)
            await interaction.response.send_message(embed=success_embed("Level-Up DM Enabled","Members will be DM\'d when they level up.\n**Preview:** " + preview))
        else:
            await interaction.response.send_message(embed=success_embed("Level-Up DM Disabled","Members will no longer receive level-up DMs."))


async def setup(bot):
    await bot.add_cog(Levels(bot))
