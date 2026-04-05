"""XERO Bot — Starboard (4 commands)"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Starboard")


class Starboard(commands.GroupCog, name="starboard"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="setup", description="Set up the starboard — messages with enough ⭐ reactions get highlighted.")
    @app_commands.describe(channel="Channel to post starred messages", threshold="Number of ⭐ reactions needed (default: 3)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def setup(self, interaction: discord.Interaction, channel: discord.TextChannel, threshold: int = 3):
        threshold = max(1, min(50, threshold))
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO starboard_config (guild_id, channel_id, threshold, enabled) VALUES (?,?,?,1)",
                (interaction.guild.id, channel.id, threshold)
            )
            await db.commit()
        await interaction.response.send_message(embed=success_embed(
            "Starboard Configured! ⭐",
            f"Messages with **{threshold}** or more ⭐ reactions will be posted in {channel.mention}.\n"
            f"React to any message with ⭐ to nominate it!"
        ))

    @app_commands.command(name="toggle", description="Enable or disable the starboard.")
    @app_commands.describe(enabled="Enable or disable")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def toggle(self, interaction: discord.Interaction, enabled: bool):
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE starboard_config SET enabled=? WHERE guild_id=?", (1 if enabled else 0, interaction.guild.id))
            await db.commit()
        status = "enabled" if enabled else "disabled"
        await interaction.response.send_message(embed=success_embed(f"Starboard {status.capitalize()}", f"Starboard is now **{status}**."))

    @app_commands.command(name="threshold", description="Change the number of ⭐ reactions required.")
    @app_commands.describe(threshold="New threshold (1-50)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def threshold(self, interaction: discord.Interaction, threshold: int):
        threshold = max(1, min(50, threshold))
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE starboard_config SET threshold=? WHERE guild_id=?", (threshold, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Threshold Updated", f"Now requires **{threshold}** ⭐ reactions to get starred."))

    @app_commands.command(name="config", description="View the current starboard configuration.")
    async def config(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM starboard_config WHERE guild_id=?", (interaction.guild.id,)) as c:
                config = await c.fetchone()
            async with db.execute("SELECT COUNT(*) FROM starboard_messages WHERE guild_id=?", (interaction.guild.id,)) as c:
                count = (await c.fetchone())[0]
        if not config:
            return await interaction.response.send_message(embed=info_embed("Not Configured", "Set up starboard with `/starboard setup`."))
        config = dict(config)
        ch = interaction.guild.get_channel(config["channel_id"])
        embed = info_embed("⭐ Starboard Configuration", "")
        embed.add_field(name="Channel", value=ch.mention if ch else "Not found", inline=True)
        embed.add_field(name="Threshold", value=f"⭐ × {config['threshold']}", inline=True)
        embed.add_field(name="Status", value="✅ Enabled" if config["enabled"] else "❌ Disabled", inline=True)
        embed.add_field(name="Total Starred", value=f"**{count:,}** messages", inline=True)
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(Starboard(bot))
