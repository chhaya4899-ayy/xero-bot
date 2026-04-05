"""XERO Bot — Backup System (5 commands)"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
import json
import datetime
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Backup")


class Backup(commands.GroupCog, name="backup"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="create", description="Create a backup of all server bot settings.")
    @app_commands.describe(name="Optional label for this backup")
    @app_commands.checks.has_permissions(administrator=True)
    @command_guard
    async def create(self, interaction: discord.Interaction, name: str = None):
        await interaction.response.defer(ephemeral=True)
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        backup_data = {
            "timestamp": datetime.datetime.now().isoformat(),
            "guild_id": interaction.guild.id,
            "guild_name": interaction.guild.name,
            "settings": settings,
        }
        backup_label = name or f"Backup {datetime.datetime.now().strftime('%Y-%m-%d %H:%M')}"
        async with aiosqlite.connect(self.bot.db.db_path) as db:
            await db.execute(
                "INSERT INTO server_backups (guild_id, backup_name, backup_data) VALUES (?,?,?)",
                (interaction.guild.id, backup_label, json.dumps(backup_data))
            )
            await db.commit()
        await interaction.followup.send(embed=success_embed("Backup Created!", f"**Name:** {backup_label}\n**Time:** {backup_data['timestamp'][:19]}"))

    @app_commands.command(name="list", description="View all saved backups for this server.")
    @app_commands.checks.has_permissions(administrator=True)
    async def list_backups(self, interaction: discord.Interaction):
        async with aiosqlite.connect(self.bot.db.db_path) as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT id, backup_name, created_at FROM server_backups WHERE guild_id=? ORDER BY created_at DESC LIMIT 10",
                (interaction.guild.id,)
            ) as c:
                backups = [dict(r) for r in await c.fetchall()]
        if not backups:
            return await interaction.response.send_message(embed=info_embed("No Backups", "No backups found. Create one with `/backup create`."))
        embed = comprehensive_embed(title="💾 Server Backups", description=f"**{len(backups)}** backup(s) found", color=discord.Color.blurple())
        for b in backups:
            ts = int(datetime.datetime.fromisoformat(b["created_at"]).timestamp())
            embed.add_field(name=f"#{b['id']} — {b['backup_name']}", value=f"Created: <t:{ts}:R>", inline=False)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="restore", description="Restore server settings from a backup by ID.")
    @app_commands.describe(backup_id="Backup ID from /backup list")
    @app_commands.checks.has_permissions(administrator=True)
    @command_guard
    async def restore(self, interaction: discord.Interaction, backup_id: int):
        await interaction.response.defer(ephemeral=True)
        async with aiosqlite.connect(self.bot.db.db_path) as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM server_backups WHERE id=? AND guild_id=?", (backup_id, interaction.guild.id)) as c:
                backup = await c.fetchone()
        if not backup:
            return await interaction.followup.send(embed=error_embed("Not Found", f"Backup #{backup_id} not found."), ephemeral=True)
        data = json.loads(backup["backup_data"])
        settings = data.get("settings", {})
        safe_keys = ["welcome_channel_id", "farewell_channel_id", "log_channel_id", "autorole_id",
                     "welcome_message", "farewell_message", "leveling_enabled", "economy_enabled",
                     "ai_enabled", "persona", "level_up_channel_id"]
        for key in safe_keys:
            if key in settings and settings[key] is not None:
                await self.bot.db.update_guild_setting(interaction.guild.id, key, settings[key])
        await interaction.followup.send(embed=success_embed("Backup Restored!", f"Settings from backup **#{backup_id}** ({backup['backup_name']}) have been restored."))

    @app_commands.command(name="delete", description="Permanently delete a backup.")
    @app_commands.describe(backup_id="Backup ID to delete")
    @app_commands.checks.has_permissions(administrator=True)
    async def delete(self, interaction: discord.Interaction, backup_id: int):
        async with aiosqlite.connect(self.bot.db.db_path) as db:
            await db.execute("DELETE FROM server_backups WHERE id=? AND guild_id=?", (backup_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Deleted", f"Backup #{backup_id} has been deleted."))

    @app_commands.command(name="export", description="Export a backup as a downloadable JSON file.")
    @app_commands.describe(backup_id="Backup ID to export")
    @app_commands.checks.has_permissions(administrator=True)
    @command_guard
    async def export(self, interaction: discord.Interaction, backup_id: int):
        await interaction.response.defer(ephemeral=True)
        async with aiosqlite.connect(self.bot.db.db_path) as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM server_backups WHERE id=? AND guild_id=?", (backup_id, interaction.guild.id)) as c:
                backup = await c.fetchone()
        if not backup:
            return await interaction.followup.send(embed=error_embed("Not Found", f"Backup #{backup_id} not found."), ephemeral=True)
        import io
        data = json.loads(backup["backup_data"])
        file_content = json.dumps(data, indent=2)
        fname = f"nexus_backup_{interaction.guild.id}_{backup_id}.json"
        file = discord.File(io.StringIO(file_content), filename=fname)
        await interaction.followup.send(embed=success_embed("Exported", f"Backup #{backup_id} exported as `{fname}`."), file=file)


async def setup(bot):
    await bot.add_cog(Backup(bot))
