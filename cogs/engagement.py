"""XERO Bot — Counting Game (5 commands) + Confessions (4 commands)"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Engagement")


class Counting(commands.GroupCog, name="counting"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="setup", description="Set a channel as the counting channel.")
    @app_commands.describe(channel="Channel to use for counting")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def setup(self, interaction: discord.Interaction, channel: discord.TextChannel):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO counting_config (guild_id, channel_id, current, last_user_id, high_score, enabled) VALUES (?,?,0,NULL,0,1)",
                (interaction.guild.id, channel.id)
            )
            await db.commit()
        embed = success_embed("Counting Channel Set!", (
            f"**{channel.mention}** is now the counting channel!\n\n"
            "Rules: type the next number in order, no two in a row from the same person, wrong number resets!"
        ))
        await channel.send(embed=discord.Embed(
            title="Counting Game Started!",
            description="Start counting from **1**! Type numbers in order. No two in a row!",
            color=discord.Color.green()
        ))
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="stats", description="View counting game stats for this server.")
    async def stats(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM counting_config WHERE guild_id=?", (interaction.guild.id,)) as c:
                configs = [dict(r) for r in await c.fetchall()]
        if not configs:
            return await interaction.response.send_message(embed=info_embed("Not Set Up", "Use `/counting setup` first."))
        embed = comprehensive_embed(title="Counting Stats", color=discord.Color.blue())
        for cfg in configs:
            ch = interaction.guild.get_channel(cfg["channel_id"])
            last_user = interaction.guild.get_member(cfg["last_user_id"]) if cfg.get("last_user_id") else None
            embed.add_field(
                name=f"#{ch.name if ch else 'Unknown'}",
                value=(
                    f"**Current:** {cfg['current']:,}\n"
                    f"**High Score:** {cfg['high_score']:,}\n"
                    f"**Last Counter:** {last_user.mention if last_user else 'None'}\n"
                    f"**Status:** {'Active' if cfg['enabled'] else 'Disabled'}"
                ),
                inline=True
            )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="reset", description="[Admin] Reset the count back to 0.")
    @app_commands.describe(channel="Channel to reset")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def reset(self, interaction: discord.Interaction, channel: discord.TextChannel = None):
        ch = channel or interaction.channel
        async with self.bot.db._db_context() as db:
            await db.execute(
                "UPDATE counting_config SET current=0, last_user_id=NULL WHERE guild_id=? AND channel_id=?",
                (interaction.guild.id, ch.id)
            )
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Count Reset", f"{ch.mention} has been reset to 0. Start from 1!"))

    @app_commands.command(name="toggle", description="[Admin] Enable or disable counting in a channel.")
    @app_commands.describe(enabled="Enable or disable")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def toggle(self, interaction: discord.Interaction, enabled: bool, channel: discord.TextChannel = None):
        ch = channel or interaction.channel
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE counting_config SET enabled=? WHERE guild_id=? AND channel_id=?",
                             (1 if enabled else 0, interaction.guild.id, ch.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed(
            f"Counting {'Enabled' if enabled else 'Disabled'}",
            f"Counting in {ch.mention} is now **{'enabled' if enabled else 'disabled'}**."
        ))

    @app_commands.command(name="leaderboard", description="View counting high scores.")
    async def leaderboard(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM counting_config WHERE guild_id=? ORDER BY high_score DESC", (interaction.guild.id,)) as c:
                configs = [dict(r) for r in await c.fetchall()]
        if not configs:
            return await interaction.response.send_message(embed=info_embed("No Data", "No counting data yet."))
        embed = comprehensive_embed(title="Counting High Scores", color=discord.Color.gold())
        for cfg in configs:
            ch = interaction.guild.get_channel(cfg["channel_id"])
            embed.add_field(name=f"#{ch.name if ch else 'Unknown'}",
                            value=f"High Score: **{cfg['high_score']:,}**\nCurrent: **{cfg['current']:,}**", inline=True)
        await interaction.response.send_message(embed=embed)


class Confessions(commands.GroupCog, name="confess"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="send", description="Send an anonymous confession to the confessions channel.")
    @app_commands.describe(message="Your anonymous confession")
    async def send(self, interaction: discord.Interaction, message: str):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        channel_id = settings.get("confession_channel_id")
        if not channel_id:
            return await interaction.response.send_message(
                embed=error_embed("Not Configured", "Ask an admin to run `/confess setup`."), ephemeral=True)
        channel = interaction.guild.get_channel(channel_id)
        if not channel:
            return await interaction.response.send_message(
                embed=error_embed("Channel Not Found", "Confessions channel not found."), ephemeral=True)
        async with self.bot.db._db_context() as db:
            async with db.execute("INSERT INTO confessions (guild_id, user_id, message) VALUES (?,?,?)",
                                  (interaction.guild.id, interaction.user.id, message)) as c:
                confession_id = c.lastrowid
            await db.commit()
        embed = comprehensive_embed(title=f"Anonymous Confession #{confession_id}", description=message, color=discord.Color.purple())
        embed.set_footer(text=f"Confession #{confession_id} | XERO Anonymous System")
        await channel.send(embed=embed)
        await interaction.response.send_message(
            embed=success_embed("Confession Sent!", "Posted anonymously. Your identity is completely hidden."),
            ephemeral=True)

    @app_commands.command(name="setup", description="[Admin] Set the confessions channel.")
    @app_commands.describe(channel="Channel for anonymous confessions")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def setup(self, interaction: discord.Interaction, channel: discord.TextChannel):
        await self.bot.db.update_guild_setting(interaction.guild.id, "confession_channel_id", channel.id)
        await interaction.response.send_message(embed=success_embed(
            "Confessions Ready!",
            f"Anonymous confessions will be posted in {channel.mention}.\nMembers use `/confess send`. Staff can use `/confess reveal` for safety."
        ))

    @app_commands.command(name="reveal", description="[Admin] Reveal who sent a confession (mod only).")
    @app_commands.describe(confession_id="Confession ID to reveal")
    @app_commands.checks.has_permissions(administrator=True)
    async def reveal(self, interaction: discord.Interaction, confession_id: int):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM confessions WHERE id=? AND guild_id=?",
                                  (confession_id, interaction.guild.id)) as c:
                confession = await c.fetchone()
        if not confession:
            return await interaction.response.send_message(
                embed=error_embed("Not Found", f"Confession #{confession_id} not found."), ephemeral=True)
        confession = dict(confession)
        user = interaction.guild.get_member(confession["user_id"])
        user_display = user.mention if user else f"Unknown (ID: {confession['user_id']})"
        embed = info_embed(f"Confession #{confession_id} — Author",
                           f"**Author:** {user_display}\n**Message:** {confession['message'][:1000]}")
        embed.set_footer(text="Confidential — moderation use only.")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="delete", description="[Admin] Delete a confession by ID.")
    @app_commands.describe(confession_id="Confession ID to delete")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def delete(self, interaction: discord.Interaction, confession_id: int):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM confessions WHERE id=? AND guild_id=?", (confession_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(
            embed=success_embed("Deleted", f"Confession #{confession_id} removed."))


async def setup(bot):
    await bot.add_cog(Counting(bot))
    await bot.add_cog(Confessions(bot))
