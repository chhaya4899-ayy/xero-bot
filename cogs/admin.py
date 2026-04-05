"""XERO Bot — Admin Dashboard (interactive panel)"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Admin")


class AdminDashboardView(discord.ui.View):
    def __init__(self, bot, guild):
        super().__init__(timeout=300)
        self.bot = bot
        self.guild = guild

    async def _set_embed(self, interaction, title, lines, color=None):
        import discord as d
        embed = d.Embed(title=title, description="\n".join(lines), color=color or d.Color.blurple())
        embed.set_footer(text="XERO Admin Panel | Click Back to return")
        await interaction.response.edit_message(embed=embed, view=BackView(self.bot, self.guild))

    @discord.ui.button(label="🛡️ Moderation", style=discord.ButtonStyle.danger, row=0)
    async def mod_btn(self, i, b):
        await self._set_embed(i, "🛡️ Moderation Commands", [
            "**`/mod warn`** — Issue a formal warning with reason",
            "**`/mod warnings`** — View all user warnings",
            "**`/mod kick`** — Kick member from server",
            "**`/mod ban`** — Ban member with optional message purge",
            "**`/mod unban`** — Unban by user ID",
            "**`/mod softban`** — Ban+unban to wipe messages",
            "**`/mod timeout`** — Timeout up to 28 days",
            "**`/mod purge`** — Bulk delete messages (up to 100)",
            "**`/mod lock`** / **`/mod unlock`** — Lock channels",
            "**`/mod history`** — View user's full mod history",
            "**`/mod nick`** — Change/reset nickname",
            "**`/mod slowmode`** — Set channel slowmode",
        ], discord.Color.red())

    @discord.ui.button(label="⚙️ Setup", style=discord.ButtonStyle.secondary, row=0)
    async def setup_btn(self, i, b):
        settings = await self.bot.db.get_guild_settings(self.guild.id)
        def ch(cid): return f"<#{cid}>" if cid else "Not set"
        def role(rid): return f"<@&{rid}>" if rid else "Not set"
        await self._set_embed(i, "⚙️ Server Configuration", [
            f"**Welcome Channel:** {ch(settings.get('welcome_channel_id'))}",
            f"**Farewell Channel:** {ch(settings.get('farewell_channel_id'))}",
            f"**Log Channel:** {ch(settings.get('log_channel_id'))}",
            f"**Auto-Role:** {role(settings.get('autorole_id'))}",
            f"**Verify Role:** {role(settings.get('verify_role_id'))}",
            f"**AI Persona:** {settings.get('persona', 'neutral')}",
            f"**Leveling:** {'✅ On' if settings.get('leveling_enabled', 1) else '❌ Off'}",
            f"**Economy:** {'✅ On' if settings.get('economy_enabled', 1) else '❌ Off'}",
            f"**AI Responses:** {'✅ On' if settings.get('ai_enabled', 1) else '❌ Off'}",
            "",
            "Use **`/settings <option>`** to change any setting.",
        ], discord.Color.blue())

    @discord.ui.button(label="🤖 AI Features", style=discord.ButtonStyle.blurple, row=0)
    async def ai_btn(self, i, b):
        await self._set_embed(i, "🤖 AI Commands (NVIDIA Llama 4 Maverick)", [
            "**`/ai ask`** — Ask any question, with optional image URL",
            "**`/ai chat`** — Context-aware multi-turn conversation",
            "**`/ai summarize`** — Summarize text or chat history",
            "**`/ai translate`** — Translate to any language",
            "**`/ai brainstorm`** — Generate creative ideas",
            "**`/ai code-explain`** — Explain code in detail",
            "**`/ai code-debug`** — Debug and fix code",
            "**`/ai sentiment`** — Deep emotional analysis",
            "**`/ai rewrite`** — Rewrite in different styles",
            "**`/ai grammar`** — Grammar and style checking",
            "**`/ai generate`** — Create any content",
            "**`/ai fact-check`** — Verify claims with AI",
            "**`/ai roast`** — Playful roast generator",
            "**`/ai analyze-image`** — Vision AI image analysis",
        ], discord.Color.purple())

    @discord.ui.button(label="💰 Economy", style=discord.ButtonStyle.success, row=0)
    async def eco_btn(self, i, b):
        await self._set_embed(i, "💰 Economy System", [
            "**`/balance`** — View wallet, bank, net worth",
            "**`/work`** — Earn money (1hr cooldown)",
            "**`/daily`** — Daily $5,000+ reward",
            "**`/weekly`** — Weekly $25-50k reward",
            "**`/deposit`** / **`/withdraw`** — Bank management",
            "**`/pay`** — Transfer money to users",
            "**`/rob`** — Risky 45% chance to steal",
            "**`/slots`** — Slot machine with jackpot",
            "**`/blackjack`** — Card game against dealer",
            "**`/coinflip`** — 50/50 bet",
            "**`/shop`** — Browse items for sale",
            "**`/buy`** — Purchase shop items",
            "**`/rich`** — Server economy leaderboard",
        ], discord.Color.gold())

    @discord.ui.button(label="🎉 Giveaways", style=discord.ButtonStyle.primary, row=1)
    async def gw_btn(self, i, b):
        await self._set_embed(i, "🎉 Giveaway System", [
            "**`/giveaway start`** — Start giveaway with prize, duration, winner count",
            "**`/giveaway end`** — Immediately end and pick winners",
            "**`/giveaway reroll`** — Pick new winners",
            "**`/giveaway list`** — View active giveaways",
            "**`/giveaway cancel`** — Cancel a giveaway",
            "**`/giveaway edit-prize`** — Change the prize",
            "**`/giveaway winners`** — View giveaway info",
            "**`/giveaway delete`** — Delete all giveaway records",
        ], discord.Color.gold())

    @discord.ui.button(label="🎫 Tickets", style=discord.ButtonStyle.secondary, row=1)
    async def ticket_btn(self, i, b):
        await self._set_embed(i, "🎫 Ticket System", [
            "**`/ticket setup`** — Post the ticket panel",
            "**`/ticket create`** — Manually create ticket for user",
            "**`/ticket close`** — Close current ticket",
            "**`/ticket add`** / **`/ticket remove`** — Add/remove users",
            "**`/ticket list`** — View all open tickets",
            "**`/ticket transcript`** — Export chat as text file",
        ], discord.Color.blurple())

    @discord.ui.button(label="✅ Verification", style=discord.ButtonStyle.success, row=1)
    async def verify_btn(self, i, b):
        await self._set_embed(i, "🛡️ Aegis Protocol", [
            "**`/verify setup`** — Deploy the 4-tier security gateway",
            "",
            "**Tiers:**",
            "1. **Silent Guard** (Click-to-Verify)",
            "2. **Secret Gate** (Custom Question)",
            "3. **Neural Link** (Math CAPTCHA)",
            "4. **Total Lockdown** (Quarantine + Appeal)",
            "",
            "*Includes real-time Silent Risk Scoring.*"
        ], discord.Color.green())

    @discord.ui.button(label="🎵 Music", style=discord.ButtonStyle.blurple, row=1)
    async def music_btn(self, i, b):
        await self._set_embed(i, "🎵 Music Player", [
            "**`/music play`** — Play from YouTube (URL or search)",
            "**`/music pause`** / **`/music resume`** — Pause control",
            "**`/music skip`** — Skip current song",
            "**`/music stop`** — Stop and disconnect",
            "**`/music queue`** — View queue",
            "**`/music nowplaying`** — Current song info",
            "**`/music volume`** — Set volume 1-100",
            "**`/music loop`** — Toggle queue loop",
            "**`/music remove`** — Remove from queue",
            "",
            "*Requires: yt-dlp & FFmpeg installed*",
        ], discord.Color.purple())

    @discord.ui.button(label="💾 Backup", style=discord.ButtonStyle.secondary, row=2)
    async def backup_btn(self, i, b):
        await self._set_embed(i, "💾 Backup & Restore", [
            "**`/backup create`** — Save current server config",
            "**`/backup list`** — View all backups",
            "**`/backup restore`** — Restore from backup by ID",
            "**`/backup delete`** — Delete a backup",
            "**`/backup export`** — Download as JSON file",
        ], discord.Color.blurple())

    @discord.ui.button(label="🛡️ AutoMod", style=discord.ButtonStyle.danger, row=2)
    async def automod_btn(self, i, b):
        await self._set_embed(i, "🛡️ AutoMod System", [
            "**`/automod setup`** — Apply recommended settings",
            "**`/automod toggle`** — Enable/disable all AutoMod",
            "**`/automod anti-spam`** — Configure spam detection",
            "**`/automod anti-links`** — Block external links",
            "**`/automod anti-caps`** — Flag excessive caps",
            "**`/automod add-filter`** — Add banned word",
            "**`/automod remove-filter`** — Remove banned word",
            "**`/automod list-filters`** — View full config",
        ], discord.Color.orange())


class BackView(discord.ui.View):
    def __init__(self, bot, guild):
        super().__init__(timeout=300)
        self.bot = bot
        self.guild = guild

    @discord.ui.button(label="← Back", style=discord.ButtonStyle.secondary)
    async def back(self, interaction, button):
        embed = _main_embed(self.guild)
        await interaction.response.edit_message(embed=embed, view=AdminDashboardView(self.bot, self.guild))


def _main_embed(guild):
    embed = discord.Embed(
        title=f"🎛️ XERO Control Panel — {guild.name}",
        description="Select a category below to explore commands and configuration.\nAll settings are live and persistent.",
        color=discord.Color.blurple()
    )
    embed.add_field(name="📊 Server", value=f"**Members:** {guild.member_count:,}", inline=True)
    embed.add_field(name="📡 Channels", value=f"**Total:** {len(guild.channels)}", inline=True)
    embed.add_field(name="🎭 Roles", value=f"**Total:** {len(guild.roles)-1}", inline=True)
    embed.set_thumbnail(url=guild.icon.url if guild.icon else None)
    embed.set_footer(text="XERO Bot | Premium features, 100% free.")
    return embed


class Admin(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="admin", description="Open the XERO interactive admin control panel.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def admin(self, interaction: discord.Interaction):
        embed = _main_embed(interaction.guild)
        view = AdminDashboardView(self.bot, interaction.guild)
        await interaction.response.send_message(embed=embed, view=view)

    @app_commands.command(name="purge-bots", description="[Admin] Delete all messages sent by bots in this channel.")
    @app_commands.describe(limit="How many messages back to scan (max 200)")
    @app_commands.checks.has_permissions(administrator=True)
    @command_guard
    async def purge_bots(self, interaction: discord.Interaction, limit: int = 100):
        limit = max(1, min(200, limit))
        await interaction.response.defer(ephemeral=True)
        deleted = await interaction.channel.purge(limit=limit, check=lambda m: m.author.bot)
        await interaction.followup.send(embed=success_embed("Bot Messages Purged", f"Deleted **{len(deleted)}** bot messages from the last {limit} messages."))

    @app_commands.command(name="shop-manage", description="Add or remove items from the server shop.")
    @app_commands.describe(action="add or remove", name="Item name", price="Item price", description="Item description", role="Role to grant on purchase", emoji="Emoji for the item")
    @app_commands.choices(action=[app_commands.Choice(name="Add Item", value="add"), app_commands.Choice(name="Remove Item", value="remove")])
    @app_commands.checks.has_permissions(administrator=True)
    async def shop_manage(self, interaction: discord.Interaction, action: str, name: str,
                          price: int = 0, description: str = "A shop item.", role: discord.Role = None, emoji: str = "🛍️"):
        import aiosqlite
        if action == "add":
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "INSERT INTO economy_shop (guild_id, name, description, price, role_id, emoji) VALUES (?,?,?,?,?,?)",
                    (interaction.guild.id, name, description, max(0, price), role.id if role else None, emoji)
                )
                await db.commit()
            embed = success_embed("Item Added to Shop!", f"**{emoji} {name}**\nPrice: ${price:,}\n{description}")
            if role:
                embed.add_field(name="Grants Role", value=role.mention, inline=True)
        else:
            async with self.bot.db._db_context() as db:
                await db.execute("DELETE FROM economy_shop WHERE guild_id=? AND LOWER(name)=LOWER(?)", (interaction.guild.id, name))
                await db.commit()
            embed = success_embed("Item Removed", f"**{name}** has been removed from the shop.")
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(Admin(bot))
