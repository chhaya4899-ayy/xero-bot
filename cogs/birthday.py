"""XERO Bot — Birthday System (7 commands)"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import datetime
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Birthday")


class Birthday(commands.GroupCog, name="birthday"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="set", description="Set your birthday so the server can celebrate with you!")
    @app_commands.describe(day="Day of birth (1-31)", month="Month of birth (1-12)", year="Year of birth (optional, for age display)")
    async def set(self, interaction: discord.Interaction, day: int, month: int, year: int = None):
        if not (1 <= day <= 31) or not (1 <= month <= 12):
            return await interaction.response.send_message(embed=error_embed("Invalid Date", "Please enter a valid day (1-31) and month (1-12)."), ephemeral=True)
        if year and not (1900 <= year <= datetime.date.today().year):
            return await interaction.response.send_message(embed=error_embed("Invalid Year", "Please enter a valid birth year."), ephemeral=True)
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO birthdays (user_id, guild_id, day, month, year, announced_year) VALUES (?,?,?,?,?,0)",
                (interaction.user.id, interaction.guild.id, day, month, year)
            )
            await db.commit()
        month_names = ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"]
        age_text = f" ({datetime.date.today().year - year} years old this year)" if year else ""
        embed = success_embed("Birthday Set! 🎂", f"Your birthday is set to **{month_names[month-1]} {day}**{age_text}.\nThe server will celebrate with you on your special day!")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="remove", description="Remove your birthday from the server.")
    async def remove(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM birthdays WHERE user_id=? AND guild_id=?", (interaction.user.id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Birthday Removed", "Your birthday has been removed from this server."))

    @app_commands.command(name="view", description="View your or another user's birthday.")
    @app_commands.describe(user="User to check birthday for")
    async def view(self, interaction: discord.Interaction, user: discord.Member = None):
        target = user or interaction.user
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM birthdays WHERE user_id=? AND guild_id=?", (target.id, interaction.guild.id)) as c:
                bday = await c.fetchone()
        if not bday:
            name = "You have" if target == interaction.user else f"{target.display_name} has"
            return await interaction.response.send_message(embed=info_embed("No Birthday Set", f"{name} not set a birthday yet."))
        bday = dict(bday)
        month_names = ["January","February","March","April","May","June","July","August","September","October","November","December"]
        # Calculate days until next birthday
        today = datetime.date.today()
        next_bday = datetime.date(today.year, bday["month"], bday["day"])
        if next_bday < today:
            next_bday = datetime.date(today.year + 1, bday["month"], bday["day"])
        days_until = (next_bday - today).days
        age_text = f"\n**Age this year:** {today.year - bday['year']}" if bday.get("year") else ""
        countdown = "🎂 **Today is their birthday!**" if days_until == 0 else f"**Next birthday:** in **{days_until}** days (<t:{int(datetime.datetime(next_bday.year, next_bday.month, next_bday.day).timestamp())}:D>)"
        embed = info_embed(
            f"🎂 {target.display_name}'s Birthday",
            f"**Date:** {month_names[bday['month']-1]} {bday['day']}{age_text}\n{countdown}",
        )
        embed.set_thumbnail(url=target.display_avatar.url)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="list", description="View all upcoming birthdays in this server.")
    async def list(self, interaction: discord.Interaction):
        today = datetime.date.today()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM birthdays WHERE guild_id=?", (interaction.guild.id,)) as c:
                birthdays = [dict(r) for r in await c.fetchall()]
        if not birthdays:
            return await interaction.response.send_message(embed=info_embed("No Birthdays", "No members have set their birthday yet. Use `/birthday set` to add yours!"))

        def days_until(m, d):
            nb = datetime.date(today.year, m, d)
            if nb < today:
                nb = datetime.date(today.year + 1, m, d)
            return (nb - today).days

        month_names = ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"]
        sorted_bdays = sorted(birthdays, key=lambda b: days_until(b["month"], b["day"]))
        embed = comprehensive_embed(title="🎂 Upcoming Birthdays", description=f"**{len(birthdays)}** birthdays registered", color=discord.Color.pink())
        for bday in sorted_bdays[:15]:
            member = interaction.guild.get_member(bday["user_id"])
            if not member:
                continue
            d = days_until(bday["month"], bday["day"])
            countdown = "🎉 **TODAY!**" if d == 0 else f"in {d} day{'s' if d != 1 else ''}"
            embed.add_field(
                name=f"{member.display_name}",
                value=f"**{month_names[bday['month']-1]} {bday['day']}** — {countdown}",
                inline=True
            )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="setup-channel", description="[Admin] Set the channel where birthday announcements are posted.")
    @app_commands.describe(channel="Birthday announcement channel", role="Optional role to give on birthdays")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def setup_channel(self, interaction: discord.Interaction, channel: discord.TextChannel, role: discord.Role = None):
        await self.bot.db.update_guild_setting(interaction.guild.id, "birthday_channel_id", channel.id)
        if role:
            await self.bot.db.update_guild_setting(interaction.guild.id, "birthday_role_id", role.id)
        role_text = f"\n**Birthday Role:** {role.mention}" if role else ""
        await interaction.response.send_message(embed=success_embed("Birthday System Configured!", f"Birthday announcements will be sent to {channel.mention}.{role_text}"))

    @app_commands.command(name="announce", description="[Admin] Manually trigger a birthday announcement for a user.")
    @app_commands.describe(user="User to celebrate")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def announce(self, interaction: discord.Interaction, user: discord.Member):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        channel_id = settings.get("birthday_channel_id") or settings.get("welcome_channel_id")
        if not channel_id:
            return await interaction.response.send_message(embed=error_embed("No Channel Set", "Set a birthday channel first with `/birthday setup-channel`."), ephemeral=True)
        channel = interaction.guild.get_channel(channel_id)
        if not channel:
            return await interaction.response.send_message(embed=error_embed("Channel Not Found", "Birthday channel not found."), ephemeral=True)
        embed = discord.Embed(
            title="🎂 Happy Birthday!",
            description=f"Everyone wish {user.mention} a very happy birthday! 🎉🎈🎊",
            color=discord.Color.pink()
        )
        embed.set_thumbnail(url=user.display_avatar.url)
        embed.set_footer(text="XERO Birthday System")
        await channel.send(content=user.mention, embed=embed)
        await interaction.response.send_message(embed=success_embed("Birthday Announced!", f"Celebrated {user.mention}'s birthday in {channel.mention}!"))

    @app_commands.command(name="today", description="See which members have a birthday today!")
    async def today(self, interaction: discord.Interaction):
        today = datetime.date.today()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM birthdays WHERE guild_id=? AND month=? AND day=?",
                (interaction.guild.id, today.month, today.day)
            ) as c:
                birthdays = [dict(r) for r in await c.fetchall()]
        if not birthdays:
            return await interaction.response.send_message(embed=info_embed("No Birthdays Today", "No members have a birthday today. 🎂"))
        members = [interaction.guild.get_member(b["user_id"]) for b in birthdays if interaction.guild.get_member(b["user_id"])]
        mentions = " ".join(m.mention for m in members if m)
        embed = success_embed(f"🎂 {len(members)} Birthday(s) Today!", f"Happy birthday to: {mentions}\n\nEvery wish them well! 🎉🎈")
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(Birthday(bot))
