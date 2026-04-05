"""
XERO Bot — Core Administration
Management-only commands for bot control, syncing, and system health.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import time
import os
import aiosqlite
import psutil
import asyncio
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed, XERO
from utils.guard import command_guard

logger = logging.getLogger("XERO.Core")

def is_management():
    async def predicate(interaction: discord.Interaction) -> bool:
        # Check against both hardcoded IDs and the MANAGEMENT_GUILD_ID from bot
        is_staff = interaction.user.id in [1124403755459346514, 1104381387601199144]
        is_mgmt_guild = interaction.guild_id == interaction.client.MANAGEMENT_GUILD_ID
        
        if not (is_staff or is_mgmt_guild):
            await interaction.response.send_message("❌ Management server or staff only.", ephemeral=True)
            return False
        return True
    return app_commands.check(predicate)

async def _ensure_mgmt_tables(db_path):
    async with aiosqlite.connect(db_path) as db:
        await db.execute("CREATE TABLE IF NOT EXISTS mgmt_logs (id INTEGER PRIMARY KEY, action TEXT, user_id INTEGER, timestamp DATETIME DEFAULT CURRENT_TIMESTAMP)")
        await db.commit()

class CoreAdmin(commands.GroupCog, name="core"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="sync", description="FORCE SYNC: Manually push the entire command tree to Discord API.")
    @is_management()
    @app_commands.describe(scope="Global or Current Guild")
    @app_commands.choices(scope=[
        app_commands.Choice(name="Global (All Servers)", value="global"),
        app_commands.Choice(name="Current Guild Only", value="guild"),
        app_commands.Choice(name="Deep Sync (All Guilds)", value="deep")
    ])
    async def sync(self, interaction: discord.Interaction, scope: str = "global"):
        await interaction.response.defer(ephemeral=True)
        try:
            if scope == "global":
                synced = await self.bot.tree.sync()
                msg = f"✅ **Global Sync Complete**\n▹ `{len(synced)}` commands pushed globally."
            elif scope == "guild":
                self.bot.tree.copy_global_to(guild=interaction.guild)
                synced = await self.bot.tree.sync(guild=interaction.guild)
                msg = f"✅ **Guild Sync Complete**\n▹ `{len(synced)}` commands pushed to **{interaction.guild.name}**."
            elif scope == "deep":
                count = 0
                for guild in self.bot.guilds:
                    try:
                        self.bot.tree.copy_global_to(guild=guild)
                        await self.bot.tree.sync(guild=guild)
                        count += 1
                    except: continue
                msg = f"✅ **Deep Sync Complete**\n▹ Pushed to `{count}` guilds."
            
            await interaction.followup.send(embed=success_embed("System Sync", msg), ephemeral=True)
        except Exception as e:
            await interaction.followup.send(embed=error_embed("Sync Failed", f"```py\n{e}\n```"), ephemeral=True)

    @app_commands.command(name="stats", description="View bot system performance and health.")
    @is_management()
    async def stats(self, interaction: discord.Interaction):
        process = psutil.Process(os.getpid())
        mem = process.memory_info().rss / 1024 / 1024
        cpu = psutil.cpu_percent()
        uptime = time.time() - self.bot.launch_time
        
        # Database size
        db_size = os.getsize(self.bot.db.db_path) / 1024 / 1024 if os.path.exists(self.bot.db.db_path) else 0
        
        desc = (
            f"**System Performance**\n"
            f"──────────────────────────\n"
            f"**Memory Usage**\n`{mem:.1f} MB` / `512 MB`\n"
            f"──────────────────────────\n"
            f"**CPU Load**\n`{cpu}%` (Optimized)\n"
            f"──────────────────────────\n"
            f"**Network Latency**\n`{round(self.bot.latency * 1000)}ms` (Elite)\n"
            f"──────────────────────────\n"
            f"**System Uptime**\n`{int(uptime // 3600)}h {int((uptime % 3600) // 60)}m`\n"
            f"──────────────────────────\n"
            f"**Global Reach**\n`{len(self.bot.guilds)}` Guilds | `{sum(g.member_count for g in self.bot.guilds):,}` Users\n"
            f"──────────────────────────\n"
            f"**Database Integrity**\n`{db_size:.2f} MB` (Aegis Protected)\n"
            f"──────────────────────────\n"
            f"**AI Engine**\n`NVIDIA Nemotron-3` (Active)"
        )
        
        embed = comprehensive_embed(
            title="XERO™ ELITE — SYSTEM DASHBOARD",
            description=f"**PERFORMANCE OVERVIEW**\n\n{desc}",
            color=XERO.PRIMARY
        )
        embed.set_footer(text=f"XERO v4.2 Elite  •  {interaction.guild.name.upper()}")
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="status", description="Check the visibility and sync status of all command groups.")
    @is_management()
    async def status(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        
        # Check global commands
        global_cmds = await self.bot.tree.fetch_commands()
        
        # Check guild commands
        mguild = discord.Object(id=self.bot.MANAGEMENT_GUILD_ID)
        guild_cmds = await self.bot.tree.fetch_commands(guild=mguild)
        
        # Check for specific groups
        groups = ["core", "ai", "branding", "ticket", "leaderboard"]
        status_lines = []
        
        for g in groups:
            is_global = any(c.name == g for c in global_cmds)
            is_guild  = any(c.name == g for c in guild_cmds)
            status_lines.append(f"▹ **/{g}**: {'✅ Global' if is_global else '❌'} | {'✅ Guild' if is_guild else '❌'}")
        
        embed = info_embed(
            "Command Sync Status",
            "Current visibility of major command groups across the network:\n\n" + "\n".join(status_lines)
        )
        embed.add_field(name="Management Guild ID", value=f"`{self.bot.MANAGEMENT_GUILD_ID}`", inline=False)
        embed.set_footer(text="Use /core sync if any group is missing.")
        
        await interaction.followup.send(embed=embed, ephemeral=True)

    @app_commands.command(name="global-config", description="Apply a configuration setting to ALL servers globally.")
    @app_commands.describe(key="The setting key (e.g., automod_enabled, welcome_channel_id)", value="The value to set")
    @is_management()
    async def global_config(self, interaction: discord.Interaction, key: str, value: str):
        await interaction.response.defer(ephemeral=True)
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute("PRAGMA table_info(guild_settings)") as c:
                    columns = [row[1] for row in await c.fetchall()]
            
            if key not in columns:
                return await interaction.followup.send(
                    embed=error_embed("Invalid Key", f"`{key}` is not a column in guild_settings."),
                    ephemeral=True
                )
            
            final = 1 if value.lower() in ("true","on","yes","1") else 0 if value.lower() in ("false","off","no","0") else (int(value) if value.isdigit() else value)
            async with self.bot.db._db_context() as db:
                await db.execute(f"UPDATE guild_settings SET {key}=?", (final,))
                await db.commit()
            
            await interaction.followup.send(embed=success_embed("Global Config", f"Successfully set `{key}` = `{final}` for all servers."), ephemeral=True)
        except Exception as e:
            logger.error(f"Global config error: {e}", exc_info=True)
            await interaction.followup.send(embed=error_embed("Error", str(e)), ephemeral=True)

    @app_commands.command(name="sql", description="[OWNER] Run a raw SQL query on the database.")
    @app_commands.describe(query="SQL query to run")
    @is_management()
    @command_guard
    async def sql(self, interaction: discord.Interaction, query: str):
        await interaction.response.defer(ephemeral=True)
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(query) as cur:
                    rows = await cur.fetchmany(20)
                await db.commit()
            if rows:
                headers = [d[0] for d in cur.description] if cur.description else []
                lines = [" | ".join(headers)] + ["─"*40] + [" | ".join(str(v) for v in row) for row in rows]
                out = "\n".join(lines)[:1800]
            else:
                out = "✅ Query executed. No rows returned."
            await interaction.followup.send(embed=discord.Embed(description=f"```\n{out}\n```", color=0x00D4FF), ephemeral=True)
        except Exception as e:
            await interaction.followup.send(embed=error_embed("SQL Error", f"```py\n{e}\n```"), ephemeral=True)

    @app_commands.command(name="broadcast", description="Send an announcement to all servers XERO is in.")
    @app_commands.describe(title="Announcement title", message="Announcement body", urgent="Ping @everyone in each server")
    @is_management()
    @command_guard
    async def broadcast(self, interaction: discord.Interaction, title: str, message: str, urgent: bool = False):
        await interaction.response.send_message(embed=discord.Embed(description=f"📡 Broadcasting to **{len(self.bot.guilds)}** servers...", color=0x00D4FF), ephemeral=True)
        embed = discord.Embed(title=f"📢  {title}", description=message, color=0x00D4FF, timestamp=discord.utils.utcnow())
        embed.set_author(name="XERO — Official Notice", icon_url=self.bot.user.display_avatar.url)
        embed.set_footer(text="XERO Bot  ·  Team Flame")
        sent = failed = 0
        for guild in self.bot.guilds:
            ch = guild.system_channel or next((c for c in guild.text_channels if guild.me.permissions_in(c).send_messages), None)
            if ch:
                try:
                    await ch.send(content="@everyone" if urgent and ch.permissions_for(guild.me).mention_everyone else None, embed=embed)
                    sent += 1
                except Exception: failed += 1
            await asyncio.sleep(0.3)
        try:
            await interaction.followup.send(embed=success_embed("Broadcast Complete", f"✅ {sent} delivered  ·  ❌ {failed} failed"), ephemeral=True)
        except Exception: pass

    @app_commands.command(name="dm-user", description="DM any user via their ID.")
    @app_commands.describe(user_id="User ID to DM", message="Message to send")
    @is_management()
    async def dm_user(self, interaction: discord.Interaction, user_id: str, message: str):
        try:
            user = await self.bot.fetch_user(int(user_id))
            await user.send(embed=discord.Embed(description=message, color=0x00D4FF, timestamp=discord.utils.utcnow()).set_footer(text="Message from XERO Team Flame"))
            await interaction.response.send_message(embed=success_embed("DM Sent", f"Message sent to **{user}**."), ephemeral=True)
        except Exception as e:
            await interaction.response.send_message(embed=error_embed("Failed", str(e)), ephemeral=True)

    @app_commands.command(name="presence", description="Change the bot's status/activity.")
    @app_commands.describe(text="Status text", activity_type="Activity type")
    @is_management()
    async def presence(self, interaction: discord.Interaction, text: str, activity_type: str = "playing"):
        act = discord.Game(name=text)
        if activity_type == "watching": act = discord.Activity(type=discord.ActivityType.watching, name=text)
        elif activity_type == "listening": act = discord.Activity(type=discord.ActivityType.listening, name=text)
        elif activity_type == "streaming": act = discord.Streaming(name=text, url="https://twitch.tv/xero")
        await self.bot.change_presence(activity=act)
        await interaction.response.send_message(embed=success_embed("Presence Updated", f"Status set to: **{activity_type.title()} {text}**"), ephemeral=True)

    @app_commands.command(name="announce", description="Post to #announcements channels across all servers.")
    @app_commands.describe(title="Title", body="Body text", ping="Ping @everyone where allowed")
    @is_management()
    @command_guard
    async def announce(self, interaction: discord.Interaction, title: str, body: str, ping: bool = False):
        await interaction.response.send_message(embed=discord.Embed(description=f"📣 Announcing to **{len(self.bot.guilds)}** servers...", color=0x00D4FF), ephemeral=True)
        embed = discord.Embed(title=f"📣  {title}", description=body, color=0x00D4FF, timestamp=discord.utils.utcnow())
        embed.set_author(name="XERO — Announcement", icon_url=self.bot.user.display_avatar.url)
        embed.set_footer(text="XERO Bot  ·  Team Flame")
        sent = failed = 0
        for guild in self.bot.guilds:
            ch = next((c for c in guild.text_channels if "announce" in c.name.lower() and guild.me.permissions_in(c).send_messages), None) or guild.system_channel
            if ch:
                try:
                    await ch.send(content="@everyone" if ping and ch.permissions_for(guild.me).mention_everyone else None, embed=embed)
                    sent += 1
                except Exception: failed += 1
            await asyncio.sleep(0.2)
        try:
            await interaction.followup.send(embed=success_embed("Announce Complete", f"✅ {sent} delivered  ·  ❌ {failed} failed"), ephemeral=True)
        except Exception: pass

async def setup(bot):
    mguild = discord.Object(id=bot.MANAGEMENT_GUILD_ID)
    await bot.add_cog(CoreAdmin(bot), guilds=[mguild])
    logger.info(f"✓ /core bound to management guild {bot.MANAGEMENT_GUILD_ID}")
