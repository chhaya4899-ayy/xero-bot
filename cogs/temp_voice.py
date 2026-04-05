"""XERO Bot — Temp Voice Channels (6 commands)
Join a trigger channel → your own private voice channel is created.
Leave → channel auto-deletes. Fully manageable.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.TempVoice")


class TempVoice(commands.GroupCog, name="tempvoice"):
    def __init__(self, bot):
        self.bot = bot

    # ── Setup ─────────────────────────────────────────────────────────────
    @app_commands.command(name="setup", description="Set up the temporary voice channel system.")
    @app_commands.describe(
        trigger_channel="The join-to-create voice channel",
        category="Category to create temp channels in (optional)",
        default_name="Default name — use {user} for member name",
        user_limit="Default user limit (0 = unlimited)"
    )
    @app_commands.checks.has_permissions(manage_guild=True)
    async def setup(self, interaction: discord.Interaction,
                    trigger_channel: discord.VoiceChannel,
                    category: discord.CategoryChannel = None,
                    default_name: str = "{user}'s Channel",
                    user_limit: int = 0):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO temp_voice_config (guild_id, trigger_channel_id, category_id, default_name, default_limit) VALUES (?,?,?,?,?)",
                (interaction.guild.id, trigger_channel.id, category.id if category else None, default_name, user_limit)
            )
            await db.commit()
        await self.bot.db.update_guild_setting(interaction.guild.id, "temp_voice_enabled", 1)
        embed = success_embed("Temp Voice Ready! 🎙️", (
            f"**Trigger Channel:** {trigger_channel.mention}\n"
            f"**Category:** {category.mention if category else 'Same as trigger'}\n"
            f"**Default Name:** `{default_name}`\n"
            f"**User Limit:** {'Unlimited' if not user_limit else user_limit}\n\n"
            "Members now join **{trigger_channel.name}** to get their own private voice channel!"
        ))
        await interaction.response.send_message(embed=embed)

    # ── Rename ────────────────────────────────────────────────────────────
    @app_commands.command(name="rename", description="Rename your temporary voice channel.")
    @app_commands.describe(name="New name for your channel")
    async def rename(self, interaction: discord.Interaction, name: str):
        if not interaction.user.voice or not interaction.user.voice.channel:
            return await interaction.response.send_message(
                embed=error_embed("Not in Voice", "You must be in your temp channel to rename it."), ephemeral=True)
        vc = interaction.user.voice.channel
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM temp_voice_channels WHERE channel_id=?", (vc.id,)) as c:
                temp = await c.fetchone()
        if not temp or dict(temp)["owner_id"] != interaction.user.id:
            return await interaction.response.send_message(
                embed=error_embed("Not Your Channel", "You can only rename your own temp channel."), ephemeral=True)
        await vc.edit(name=name[:100])
        await interaction.response.send_message(embed=success_embed("Channel Renamed", f"Your channel is now **{name}**."))

    # ── Limit ─────────────────────────────────────────────────────────────
    @app_commands.command(name="limit", description="Set the user limit for your temporary voice channel.")
    @app_commands.describe(limit="Max users (0 = unlimited)")
    async def limit(self, interaction: discord.Interaction, limit: int):
        if not interaction.user.voice or not interaction.user.voice.channel:
            return await interaction.response.send_message(
                embed=error_embed("Not in Voice", "Join your temp channel first."), ephemeral=True)
        vc = interaction.user.voice.channel
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT owner_id FROM temp_voice_channels WHERE channel_id=?", (vc.id,)) as c:
                row = await c.fetchone()
        if not row or row[0] != interaction.user.id:
            return await interaction.response.send_message(
                embed=error_embed("Not Your Channel", "You can only modify your own temp channel."), ephemeral=True)
        limit = max(0, min(99, limit))
        await vc.edit(user_limit=limit)
        await interaction.response.send_message(embed=success_embed(
            "Limit Updated",
            f"Your channel now allows **{'unlimited' if limit == 0 else limit}** users."
        ))

    # ── Lock / Unlock ─────────────────────────────────────────────────────
    @app_commands.command(name="lock", description="Lock your temp voice channel so only you can invite people.")
    async def lock(self, interaction: discord.Interaction):
        if not interaction.user.voice or not interaction.user.voice.channel:
            return await interaction.response.send_message(embed=error_embed("Not in Voice", "Join your channel first."), ephemeral=True)
        vc = interaction.user.voice.channel
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT owner_id FROM temp_voice_channels WHERE channel_id=?", (vc.id,)) as c:
                row = await c.fetchone()
        if not row or row[0] != interaction.user.id:
            return await interaction.response.send_message(embed=error_embed("Not Owner", "Only the channel owner can lock it."), ephemeral=True)
        overwrite = vc.overwrites_for(interaction.guild.default_role)
        overwrite.connect = False
        await vc.set_permissions(interaction.guild.default_role, overwrite=overwrite)
        await interaction.response.send_message(embed=success_embed("Channel Locked 🔒", "Your temp channel is now locked. Only invited users can join."))

    @app_commands.command(name="unlock", description="Unlock your temp voice channel for everyone to join.")
    async def unlock(self, interaction: discord.Interaction):
        if not interaction.user.voice or not interaction.user.voice.channel:
            return await interaction.response.send_message(embed=error_embed("Not in Voice", "Join your channel first."), ephemeral=True)
        vc = interaction.user.voice.channel
        overwrite = vc.overwrites_for(interaction.guild.default_role)
        overwrite.connect = None
        await vc.set_permissions(interaction.guild.default_role, overwrite=overwrite)
        await interaction.response.send_message(embed=success_embed("Channel Unlocked 🔓", "Your temp channel is now open for everyone."))

    # ── Active ────────────────────────────────────────────────────────────
    @app_commands.command(name="active", description="View all active temp voice channels in the server.")
    async def active(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM temp_voice_channels WHERE guild_id=?", (interaction.guild.id,)) as c:
                channels = [dict(r) for r in await c.fetchall()]
        if not channels:
            return await interaction.response.send_message(embed=info_embed("No Active Channels", "No temp voice channels are currently active."))
        embed = comprehensive_embed(title=f"🎙️ Active Temp Channels ({len(channels)})", color=discord.Color.blurple())
        for ch_data in channels:
            vc = interaction.guild.get_channel(ch_data["channel_id"])
            owner = interaction.guild.get_member(ch_data["owner_id"])
            if vc:
                embed.add_field(
                    name=vc.name,
                    value=f"**Owner:** {owner.mention if owner else 'Unknown'}\n**Members:** {len(vc.members)}/{vc.user_limit or '∞'}",
                    inline=True
                )
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(TempVoice(bot))
