"""XERO Bot — Server Setup & Configuration (12 commands)"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed, brand_embed

logger = logging.getLogger("XERO.Setup")


class Setup(commands.GroupCog, name="settings"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="welcome-channel", description="Configure the welcome message system.")
    @app_commands.describe(
        channel="Channel to send welcome messages", 
        message="Message ({user}=mention, {server}=name, {count}=member count)",
        use_brand_image="Whether to use the Unified Brand Image (True) or a custom image (False)",
        custom_image="Custom image URL to use for welcome messages (if use_brand_image is False)"
    )
    @app_commands.checks.has_permissions(manage_guild=True)
    async def welcome(self, interaction: discord.Interaction, channel: discord.TextChannel, 
                      message: str = None, use_brand_image: bool = True, custom_image: str = None):
        await self.bot.db.update_guild_setting(interaction.guild.id, "welcome_channel_id", channel.id)
        if message:
            await self.bot.db.update_guild_setting(interaction.guild.id, "welcome_message", message)
        
        await self.bot.db.update_guild_setting(interaction.guild.id, "welcome_use_brand", 1 if use_brand_image else 0)
        if custom_image:
            await self.bot.db.update_guild_setting(interaction.guild.id, "welcome_custom_image", custom_image)
            
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        preview_text = (message or settings.get("welcome_message", "Welcome {user}!")).replace("{user}", interaction.user.mention).replace("{server}", interaction.guild.name).replace("{count}", str(interaction.guild.member_count))
        
        embed = success_embed("Welcome System Configured", f"**Channel:** {channel.mention}\n**Message Preview:**\n{preview_text}")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="farewell", description="Configure the farewell message system.")
    @app_commands.describe(channel="Channel to send farewell messages", message="Message ({user}=name, {server}=name)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def farewell(self, interaction: discord.Interaction, channel: discord.TextChannel, message: str = None):
        await self.bot.db.update_guild_setting(interaction.guild.id, "farewell_channel_id", channel.id)
        if message:
            await self.bot.db.update_guild_setting(interaction.guild.id, "farewell_message", message)
        await interaction.response.send_message(embed=success_embed("Farewell System Configured", f"**Channel:** {channel.mention}"))

    @app_commands.command(name="log-channel", description="Set the moderation & bot log channel.")
    @app_commands.describe(channel="Channel to send logs to")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def logs(self, interaction: discord.Interaction, channel: discord.TextChannel):
        await self.bot.db.update_guild_setting(interaction.guild.id, "log_channel_id", channel.id)
        await interaction.response.send_message(embed=success_embed("Log Channel Set", f"All mod actions and bot events will be logged to {channel.mention}."))

    @app_commands.command(name="autorole", description="Set a role to automatically assign when members join.")
    @app_commands.describe(role="Role to auto-assign (leave empty to disable)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def autorole(self, interaction: discord.Interaction, role: discord.Role = None):
        await self.bot.db.update_guild_setting(interaction.guild.id, "autorole_id", role.id if role else None)
        if role:
            await interaction.response.send_message(embed=success_embed("Auto-Role Set", f"New members will receive {role.mention} on join."))
        else:
            await interaction.response.send_message(embed=success_embed("Auto-Role Disabled", "New members will no longer receive an automatic role."))

    @app_commands.command(name="muterole", description="Set a dedicated mute role for the server.")
    @app_commands.describe(role="Role to use as mute role")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def muterole(self, interaction: discord.Interaction, role: discord.Role):
        await self.bot.db.update_guild_setting(interaction.guild.id, "mute_role_id", role.id)
        await interaction.response.send_message(embed=success_embed("Mute Role Set", f"{role.mention} will be used as the mute role."))

    @app_commands.command(name="leveling-toggle", description="Enable or disable the leveling/XP system.")
    @app_commands.describe(enabled="Enable or disable leveling")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def leveling(self, interaction: discord.Interaction, enabled: bool):
        await self.bot.db.update_guild_setting(interaction.guild.id, "leveling_enabled", 1 if enabled else 0)
        status = "enabled" if enabled else "disabled"
        await interaction.response.send_message(embed=success_embed(f"Leveling {status.capitalize()}", f"The XP and leveling system is now **{status}**."))

    @app_commands.command(name="economy-toggle", description="Enable or disable the economy system.")
    @app_commands.describe(enabled="Enable or disable economy")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def economy(self, interaction: discord.Interaction, enabled: bool):
        await self.bot.db.update_guild_setting(interaction.guild.id, "economy_enabled", 1 if enabled else 0)
        status = "enabled" if enabled else "disabled"
        await interaction.response.send_message(embed=success_embed(f"Economy {status.capitalize()}", f"The economy system is now **{status}**."))

    @app_commands.command(name="ai-responses", description="Enable or disable AI responses when the bot is mentioned.")
    @app_commands.describe(enabled="Enable or disable AI mention responses")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def ai_responses(self, interaction: discord.Interaction, enabled: bool):
        await self.bot.db.update_guild_setting(interaction.guild.id, "ai_enabled", 1 if enabled else 0)
        status = "enabled" if enabled else "disabled"
        await interaction.response.send_message(embed=success_embed(f"AI Responses {status.capitalize()}", f"AI responses when mentioning the bot are now **{status}**."))

    @app_commands.command(name="levelup-channel", description="Set a dedicated channel for level-up announcements.")
    @app_commands.describe(channel="Channel for level-up messages (leave empty to announce in message channel)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def levelup_channel(self, interaction: discord.Interaction, channel: discord.TextChannel = None):
        await self.bot.db.update_guild_setting(interaction.guild.id, "level_up_channel_id", channel.id if channel else None)
        if channel:
            await interaction.response.send_message(embed=success_embed("Level-Up Channel Set", f"Level-up announcements will be sent to {channel.mention}."))
        else:
            await interaction.response.send_message(embed=success_embed("Level-Up Channel Cleared", "Level-up messages will appear in the channel where the user chatted."))

    @app_commands.command(name="ai-persona", description="Set the AI personality for this server.")
    @app_commands.describe(persona="Personality style for AI responses")
    @app_commands.choices(persona=[
        app_commands.Choice(name="Neutral (Default)", value="neutral"),
        app_commands.Choice(name="Friendly & Warm", value="friendly"),
        app_commands.Choice(name="Analytical & Data-Driven", value="analytical"),
        app_commands.Choice(name="Sarcastic & Witty", value="sarcastic"),
        app_commands.Choice(name="Mentor & Wise", value="mentor"),
    ])
    @app_commands.checks.has_permissions(manage_guild=True)
    async def ai_persona(self, interaction: discord.Interaction, persona: str):
        await self.bot.db.update_guild_setting(interaction.guild.id, "persona", persona)
        persona_descriptions = {
            "neutral": "Professional and balanced responses",
            "friendly": "Warm, casual, and enthusiastic",
            "analytical": "Highly detailed and data-driven",
            "sarcastic": "Clever and witty",
            "mentor": "Wise and encouraging"
        }
        await interaction.response.send_message(embed=success_embed("AI Persona Updated", f"**Persona:** {persona.capitalize()}\n**Style:** {persona_descriptions.get(persona, '')}"))

    @app_commands.command(name="status", description="View the current server configuration.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def view(self, interaction: discord.Interaction):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)

        def ch_mention(cid): return f"<#{cid}>" if cid else "Not set"
        def role_mention(rid): return f"<@&{rid}>" if rid else "Not set"
        def toggle(val): return "✅ Enabled" if val else "❌ Disabled"

        embed = comprehensive_embed(
            title=f"⚙️ Server Configuration — {interaction.guild.name}",
            description="Current XERO bot settings for this server.",
            color=discord.Color.blurple(),
            thumbnail_url=interaction.guild.icon.url if interaction.guild.icon else None
        )
        embed.add_field(name="📢 Channels", value=(
            f"**Welcome:** {ch_mention(settings.get('welcome_channel_id'))}\n"
            f"**Farewell:** {ch_mention(settings.get('farewell_channel_id'))}\n"
            f"**Logs:** {ch_mention(settings.get('log_channel_id'))}\n"
            f"**Level-Up:** {ch_mention(settings.get('level_up_channel_id'))}"
        ), inline=True)
        embed.add_field(name="🎭 Roles", value=(
            f"**Auto-Role:** {role_mention(settings.get('autorole_id'))}\n"
            f"**Mute Role:** {role_mention(settings.get('mute_role_id'))}\n"
            f"**Verify Role:** {role_mention(settings.get('verify_role_id'))}"
        ), inline=True)
        embed.add_field(name="🔧 Features", value=(
            f"**Leveling:** {toggle(settings.get('leveling_enabled', 1))}\n"
            f"**Economy:** {toggle(settings.get('economy_enabled', 1))}\n"
            f"**AI Responses:** {toggle(settings.get('ai_enabled', 1))}\n"
            f"**AutoMod:** {toggle(settings.get('automod_enabled', 0))}"
        ), inline=True)
        embed.add_field(name="🤖 AI", value=(
            f"**Persona:** {settings.get('persona', 'neutral').capitalize()}"
        ), inline=False)
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(Setup(bot))
