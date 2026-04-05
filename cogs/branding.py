"""XERO Bot — Unified Branding & Customization"""
import discord
from discord.ext import commands, tasks
from discord import app_commands
import aiosqlite
import io
import logging
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Branding")

class Branding(commands.GroupCog, name="branding"):
    def __init__(self, bot):
        self.bot = bot
        self.auto_apply_banners.start()

    def cog_unload(self):
        self.auto_apply_banners.cancel()

    @tasks.loop(hours=24)
    async def auto_apply_banners(self):
        """Auto-applies the biggest file from the banner channel on restart/daily."""
        await self.bot.wait_until_ready()
        for guild in self.bot.guilds:
            try:
                settings = await self.bot.db.get_guild_settings(guild.id)
                channel_id = settings.get("banner_channel_id")
                if channel_id:
                    channel = guild.get_channel(int(channel_id))
                    if channel:
                        await self._apply_latest_banner(guild, channel)
            except Exception as e:
                logger.error(f"Auto-apply banner error for {guild.id}: {e}")

    async def _apply_latest_banner(self, guild, channel):
        """Helper to find and apply the largest image from a channel."""
        best_url = None
        max_size = 0
        async for message in channel.history(limit=50):
            for attachment in message.attachments:
                if attachment.content_type and attachment.content_type.startswith("image/"):
                    if attachment.size > max_size:
                        max_size = attachment.size
                        best_url = attachment.url
        
        if best_url:
            await self.bot.db.update_guild_setting(guild.id, "unified_image_url", best_url)
            logger.info(f"Applied banner for {guild.name}: {best_url} ({max_size} bytes)")
            return best_url
        return None

    @app_commands.command(name="setup-channel", description="Set the channel where the bot will save and fetch the unified banner image.")
    @app_commands.describe(channel="The channel to use for banner storage")
    @app_commands.checks.has_permissions(administrator=True)
    async def setup_channel(self, interaction: discord.Interaction, channel: discord.TextChannel):
        await self.bot.db.update_guild_setting(interaction.guild.id, "banner_channel_id", str(channel.id))
        await interaction.response.send_message(embed=success_embed("Banner Channel Set", f"The bot will now save and fetch banners from {channel.mention}.\nUpload an image there and use `/branding apply` to set it!"))

    @app_commands.command(name="apply", description="Manually trigger the auto-apply logic to fetch the biggest image from the banner channel.")
    @app_commands.checks.has_permissions(administrator=True)
    async def apply_banner(self, interaction: discord.Interaction):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        channel_id = settings.get("banner_channel_id")
        if not channel_id:
            return await interaction.response.send_message(embed=error_embed("Not Setup", "Please set a banner channel first using `/branding setup-channel`."), ephemeral=True)
        
        channel = interaction.guild.get_channel(int(channel_id))
        if not channel:
            return await interaction.response.send_message(embed=error_embed("Channel Not Found", "The configured banner channel no longer exists."), ephemeral=True)
        
        await interaction.response.defer()
        url = await self._apply_latest_banner(interaction.guild, channel)
        
        if url:
            embed = success_embed("Banner Applied", "The largest image from the banner channel has been applied to all modules.")
            embed.set_image(url=url)
            await interaction.followup.send(embed=embed)
        else:
            await interaction.followup.send(embed=error_embed("No Image Found", "No images were found in the banner channel."))

    @app_commands.command(name="set", description="Upload a new unified banner image. It will be saved to the banner channel and applied.")
    @app_commands.describe(image="The image to use (upload a file)")
    @app_commands.checks.has_permissions(administrator=True)
    async def set_banner(self, interaction: discord.Interaction, image: discord.Attachment):
        if not image.content_type or not image.content_type.startswith("image/"):
            return await interaction.response.send_message(embed=error_embed("Invalid File", "Please upload a valid image file."), ephemeral=True)
        
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        channel_id = settings.get("banner_channel_id")
        
        await interaction.response.defer()
        
        # If channel is set, save it there first
        if channel_id:
            channel = interaction.guild.get_channel(int(channel_id))
            if channel:
                # Re-upload to the storage channel to ensure it stays there
                img_bytes = await image.read()
                file = discord.File(io.BytesIO(img_bytes), filename=image.filename)
                msg = await channel.send(content=f"New Unified Banner uploaded by {interaction.user}", file=file)
                # Use the new URL from our storage channel
                final_url = msg.attachments[0].url
            else:
                final_url = image.url
        else:
            final_url = image.url

        await self.bot.db.update_guild_setting(interaction.guild.id, "unified_image_url", final_url)
        
        modules = ["Tickets", "Verification", "Welcome", "Leaderboards", "Economy", "Level-Up"]
        module_list = "\n".join([f"──────────────────────────\n**{m}**" for m in modules])
        
        desc = (
            f"**Branding Deployment**\n"
            f"This image is now the pride of your server and will be used across:\n\n"
            f"{module_list}\n"
            f"──────────────────────────"
        )
        
        embed = success_embed(
            title="XERO™ ELITE — UNIFIED BRANDING ACTIVE",
            description=f"**BRANDING DEPLOYED**\n\n{desc}",
            color=XERO.SUCCESS
        )
        embed.set_image(url=final_url)
        if not channel_id:
            embed.set_footer(text="Tip: Use /branding setup-channel to ensure this persists forever!")
        
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="view", description="View your server's branding configuration.")
    async def view_branding(self, interaction: discord.Interaction):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        
        channel_id = settings.get("banner_channel_id")
        channel_mention = f"<#{channel_id}>" if channel_id else "Not Set"
        image_url = settings.get("unified_image_url")
        
        desc = (
            f"**Branding Configuration**\n"
            f"──────────────────────────\n"
            f"**Embed Color**\n`{settings.get('embed_color', '#00D4FF')}`\n"
            f"──────────────────────────\n"
            f"**Storage Channel**\n{channel_mention}\n"
            f"──────────────────────────\n"
            f"**Unified Image**\n{'Active' if image_url else 'None'}\n"
            f"──────────────────────────"
        )
        
        embed = info_embed(
            title="XERO™ ELITE — BRANDING OVERVIEW",
            description=f"**CUSTOMIZATION SETTINGS**\n\n{desc}",
            color=XERO.PRIMARY
        )
        
        if image_url:
            embed.set_image(url=image_url)
            
        await interaction.response.send_message(embed=embed)

async def setup(bot):
    await bot.add_cog(Branding(bot))
