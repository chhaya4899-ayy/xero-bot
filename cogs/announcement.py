"""XERO Bot — Announcements (7 commands)"""
import discord
from discord.ext import commands, tasks
from discord import app_commands
import logging
import datetime
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Announcement")


class Announcement(commands.GroupCog, name="announcement"):
    def __init__(self, bot):
        self.bot = bot
        self.process_announcements.start()

    def cog_unload(self):
        self.process_announcements.cancel()

    @tasks.loop(minutes=1)
    async def process_announcements(self):
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM announcements WHERE sent=0 AND scheduled_time <= datetime('now')"
                ) as c:
                    pending = [dict(r) for r in await c.fetchall()]
            for ann in pending:
                try:
                    ch = self.bot.get_channel(ann["channel_id"])
                    if ch:
                        from utils.embeds import brand_embed, comprehensive_embed
                        embed = comprehensive_embed(title=f"📢 {ann['title']}", description=ann["message"], color=discord.Color.blurple())
                        embed.set_footer(text="Scheduled Announcement")
                        
                        # Unified Branding
                        embed, file = await brand_embed(embed, ch.guild, self.bot)
                        if file:
                            await ch.send(embed=embed, file=file)
                        else:
                            await ch.send(embed=embed)
                    async with self.bot.db._db_context() as db:
                        await db.execute("UPDATE announcements SET sent=1 WHERE announcement_id=?", (ann["announcement_id"],))
                        await db.commit()
                except Exception as e:
                    logger.error(f"Announcement send error: {e}")
        except Exception as e:
            logger.error(f"Announcement loop error: {e}")

    @process_announcements.before_loop
    async def before_loop(self):
        await self.bot.wait_until_ready()

    @app_commands.command(name="send", description="Send an announcement immediately to a channel.")
    @app_commands.describe(channel="Target channel", title="Announcement title", message="Announcement body", ping_everyone="Ping @everyone with the announcement", color="Embed color")
    @app_commands.choices(color=[
        app_commands.Choice(name="Blue (Default)", value="blue"),
        app_commands.Choice(name="Red", value="red"),
        app_commands.Choice(name="Green", value="green"),
        app_commands.Choice(name="Gold", value="gold"),
        app_commands.Choice(name="Purple", value="purple"),
    ])
    @app_commands.checks.has_permissions(manage_messages=True)
    async def send(self, interaction: discord.Interaction, channel: discord.TextChannel, title: str, message: str,
                   ping_everyone: bool = False, color: str = "blue"):
        color_map = {"blue": discord.Color.blue(), "red": discord.Color.red(), "green": discord.Color.green(),
                     "gold": discord.Color.gold(), "purple": discord.Color.purple()}
        from utils.embeds import brand_embed, comprehensive_embed
        embed = comprehensive_embed(title=f"📢 {title}", description=message, color=color_map.get(color, discord.Color.blue()))
        embed.set_footer(text=f"Announced by {interaction.user.display_name}")
        content = "@everyone" if ping_everyone else None
        
        # Unified Branding
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        if file:
            await channel.send(content=content, embed=embed, file=file)
        else:
            await channel.send(content=content, embed=embed)
        await interaction.response.send_message(embed=success_embed("Announcement Sent!", f"**{title}** posted in {channel.mention}."))

    @app_commands.command(name="schedule", description="Schedule an announcement for a future time.")
    @app_commands.describe(channel="Target channel", title="Announcement title", message="Announcement body", minutes_from_now="Minutes from now to send")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def schedule(self, interaction: discord.Interaction, channel: discord.TextChannel, title: str, message: str, minutes_from_now: int = 60):
        minutes_from_now = max(1, min(43200, minutes_from_now))
        scheduled_time = datetime.datetime.utcnow() + datetime.timedelta(minutes=minutes_from_now)
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT INTO announcements (guild_id, channel_id, title, message, scheduled_time, created_by) VALUES (?,?,?,?,?,?)",
                (interaction.guild.id, channel.id, title, message, scheduled_time, interaction.user.id)
            )
            await db.commit()
        end_ts = int(scheduled_time.timestamp())
        await interaction.response.send_message(embed=success_embed("Announcement Scheduled!", f"**{title}** will be posted in {channel.mention} <t:{end_ts}:R>."))

    @app_commands.command(name="list", description="View all pending scheduled announcements.")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def list_announcements(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM announcements WHERE guild_id=? AND sent=0 ORDER BY scheduled_time ASC", (interaction.guild.id,)) as c:
                anns = [dict(r) for r in await c.fetchall()]
        if not anns:
            return await interaction.response.send_message(embed=info_embed("No Pending Announcements", "No scheduled announcements found."))
        embed = comprehensive_embed(title="📢 Pending Announcements", description=f"**{len(anns)}** scheduled", color=discord.Color.blurple())
        for ann in anns[:8]:
            ch = interaction.guild.get_channel(ann["channel_id"])
            ts = int(datetime.datetime.fromisoformat(ann["scheduled_time"]).timestamp())
            embed.add_field(
                name=f"#{ann['announcement_id']} — {ann['title']}",
                value=f"**Channel:** {ch.mention if ch else 'Unknown'}\n**Sends:** <t:{ts}:R>",
                inline=False
            )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="cancel", description="Cancel a pending scheduled announcement.")
    @app_commands.describe(announcement_id="ID of the announcement to cancel")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def cancel(self, interaction: discord.Interaction, announcement_id: int):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM announcements WHERE announcement_id=? AND guild_id=?", (announcement_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Cancelled", f"Announcement **#{announcement_id}** has been cancelled."))

    @app_commands.command(name="edit", description="Edit a pending scheduled announcement's message.")
    @app_commands.describe(announcement_id="ID to edit", new_title="New title (optional)", new_message="New message body")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def edit(self, interaction: discord.Interaction, announcement_id: int, new_message: str, new_title: str = None):
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE announcements SET message=? WHERE announcement_id=? AND guild_id=?", (new_message, announcement_id, interaction.guild.id))
            if new_title:
                await db.execute("UPDATE announcements SET title=? WHERE announcement_id=? AND guild_id=?", (new_title, announcement_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Announcement Edited", f"Announcement **#{announcement_id}** has been updated."))

    @app_commands.command(name="mention-role", description="Send an announcement that pings a specific role.")
    @app_commands.describe(role="Role to mention", channel="Target channel", title="Title", message="Message body")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def mention_role(self, interaction: discord.Interaction, role: discord.Role, channel: discord.TextChannel, title: str, message: str):
        embed = comprehensive_embed(title=f"📢 {title}", description=message, color=discord.Color.blurple())
        embed.set_footer(text=f"Announced by {interaction.user.display_name} | XERO Bot")
        await channel.send(content=role.mention, embed=embed)
        await interaction.response.send_message(embed=success_embed("Announcement Sent!", f"Announcement sent with {role.mention} in {channel.mention}."))

    @app_commands.command(name="set-channel", description="Set the default announcement channel for the server.")
    @app_commands.describe(channel="Default channel for announcements")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def set_channel(self, interaction: discord.Interaction, channel: discord.TextChannel):
        # BUG FIX: This was overwriting welcome_channel_id. 
        # Since there is no dedicated announcement_channel_id in the schema yet, 
        # we'll use a new key and the DB will auto-add the column.
        await self.bot.db.update_guild_setting(interaction.guild.id, "announcement_channel_id", channel.id)
        await interaction.response.send_message(embed=success_embed("Default Channel Set", f"Default announcement channel set to {channel.mention}."))


async def setup(bot):
    await bot.add_cog(Announcement(bot))
