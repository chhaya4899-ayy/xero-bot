"""XERO Bot — Advanced Info & Profile Commands (12 commands)"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
import datetime
import urllib.parse
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Profile")


class Profile(commands.GroupCog, name="profile"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="card", description="View a full XERO profile card for yourself or another user.")
    @app_commands.describe(user="User to view profile for")
    async def card(self, interaction: discord.Interaction, user: discord.Member = None):
        target = user or interaction.user
        level_data = await self.bot.db.get_level(target.id, interaction.guild.id)
        eco_data = await self.bot.db.get_economy(target.id, interaction.guild.id)
        stats_data = await self.bot.db.get_user_stats(target.id, interaction.guild.id)
        warns = await self.bot.db.get_warnings(interaction.guild.id, target.id)
        cases = await self.bot.db.get_mod_cases(interaction.guild.id, target.id, limit=1)
        level = level_data.get("level", 0)
        total_xp = level_data.get("total_xp", 0)
        wallet = eco_data.get("wallet", 0)
        bank = eco_data.get("bank", 0)
        next_xp = ((level + 1) ** 2) * 100
        curr_xp = level_data.get("xp", 0)
        bar_fill = min(int((curr_xp / max(next_xp, 1)) * 15), 15)
        xp_bar = "█" * bar_fill + "░" * (15 - bar_fill)
        badges = []
        if target.id == interaction.guild.owner_id: badges.append("👑")
        if target.guild_permissions.administrator: badges.append("🛡️")
        if target.premium_since: badges.append("💎")
        if target.bot: badges.append("🤖")
        if level >= 50: badges.append("🔥")
        if level >= 25: badges.append("⭐")
        embed = discord.Embed(
            title=f"{''.join(badges)} {target.display_name}'s Profile",
            color=target.color if target.color.value else discord.Color.blurple()
        )
        embed.set_thumbnail(url=target.display_avatar.url)
        embed.add_field(name="📋 Account", value=(
            f"**Username:** {target}\n"
            f"**ID:** `{target.id}`\n"
            f"**Joined:** <t:{int(target.joined_at.timestamp())}:R>"
        ), inline=True)
        embed.add_field(name="📊 Levels", value=(
            f"**Level:** {level}\n"
            f"**Total XP:** {total_xp:,}\n"
            f"`{xp_bar}` {curr_xp}/{next_xp}"
        ), inline=True)
        embed.add_field(name="💰 Economy", value=(
            f"**Wallet:** ${wallet:,}\n"
            f"**Bank:** ${bank:,}\n"
            f"**Net Worth:** ${wallet+bank:,}"
        ), inline=True)
        embed.add_field(name="📈 Activity", value=(
            f"**Commands Used:** {stats_data.get('commands_used', 0):,}\n"
            f"**Messages Sent:** {stats_data.get('messages_sent', 0):,}\n"
            f"**Warnings:** {len(warns)}"
        ), inline=True)
        embed.add_field(name="🎭 Roles", value=f"**{len(target.roles)-1}** roles | Top: {target.top_role.mention}", inline=True)
        embed.set_footer(text=f"XERO Profile | {interaction.guild.name}")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="achievements", description="View your unlocked XERO achievements.")
    @app_commands.describe(user="User to check achievements for")
    async def achievements(self, interaction: discord.Interaction, user: discord.Member = None):
        target = user or interaction.user
        level_data = await self.bot.db.get_level(target.id, interaction.guild.id)
        eco_data = await self.bot.db.get_economy(target.id, interaction.guild.id)
        stats_data = await self.bot.db.get_user_stats(target.id, interaction.guild.id)
        level = level_data.get("level", 0)
        total_earned = eco_data.get("total_earned", 0)
        cmds = stats_data.get("commands_used", 0)
        all_achievements = [
            ("🌱 First Steps", "Used your first command", cmds >= 1),
            ("📊 Active Member", "Used 50+ commands", cmds >= 50),
            ("🔥 Power User", "Used 500+ commands", cmds >= 500),
            ("⭐ Rising Star", "Reached Level 5", level >= 5),
            ("🌟 Legend", "Reached Level 25", level >= 25),
            ("💎 Elite", "Reached Level 50", level >= 50),
            ("👶 Broke No More", "Earned $10,000 total", total_earned >= 10000),
            ("💵 Money Maker", "Earned $100,000 total", total_earned >= 100000),
            ("🤑 Millionaire", "Earned $1,000,000 total", total_earned >= 1000000),
        ]
        unlocked = [(name, desc) for name, desc, condition in all_achievements if condition]
        locked = [(name, desc) for name, desc, condition in all_achievements if not condition]
        embed = comprehensive_embed(
            title=f"🏆 {target.display_name}'s Achievements",
            description=f"**{len(unlocked)}/{len(all_achievements)}** unlocked",
            color=discord.Color.gold(),
            thumbnail_url=target.display_avatar.url
        )
        if unlocked:
            embed.add_field(name="✅ Unlocked", value="\n".join(f"**{n}** — {d}" for n, d in unlocked), inline=False)
        if locked:
            embed.add_field(name="🔒 Locked", value="\n".join(f"~~{n}~~ — {d}" for n, d in locked[:5]), inline=False)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="compare", description="Compare two users' stats side by side.")
    @app_commands.describe(user1="First user", user2="Second user (default: yourself)")
    async def compare(self, interaction: discord.Interaction, user1: discord.Member, user2: discord.Member = None):
        u2 = user2 or interaction.user
        d1_lvl = await self.bot.db.get_level(user1.id, interaction.guild.id)
        d2_lvl = await self.bot.db.get_level(u2.id, interaction.guild.id)
        d1_eco = await self.bot.db.get_economy(user1.id, interaction.guild.id)
        d2_eco = await self.bot.db.get_economy(u2.id, interaction.guild.id)
        d1_stats = await self.bot.db.get_user_stats(user1.id, interaction.guild.id)
        d2_stats = await self.bot.db.get_user_stats(u2.id, interaction.guild.id)

        def winner(a, b): return "🏆" if a > b else ("🤝" if a == b else "")

        embed = comprehensive_embed(title=f"⚔️ {user1.display_name} vs {u2.display_name}", color=discord.Color.blurple())
        embed.add_field(name=f"📊 Level", value=(
            f"{user1.display_name}: **{d1_lvl.get('level',0)}** {winner(d1_lvl.get('level',0), d2_lvl.get('level',0))}\n"
            f"{u2.display_name}: **{d2_lvl.get('level',0)}** {winner(d2_lvl.get('level',0), d1_lvl.get('level',0))}"
        ), inline=True)
        nw1 = d1_eco.get("wallet", 0) + d1_eco.get("bank", 0)
        nw2 = d2_eco.get("wallet", 0) + d2_eco.get("bank", 0)
        embed.add_field(name="💰 Net Worth", value=(
            f"{user1.display_name}: **${nw1:,}** {winner(nw1, nw2)}\n"
            f"{u2.display_name}: **${nw2:,}** {winner(nw2, nw1)}"
        ), inline=True)
        c1, c2 = d1_stats.get("commands_used", 0), d2_stats.get("commands_used", 0)
        embed.add_field(name="🔧 Commands", value=(
            f"{user1.display_name}: **{c1:,}** {winner(c1, c2)}\n"
            f"{u2.display_name}: **{c2:,}** {winner(c2, c1)}"
        ), inline=True)
        await interaction.response.send_message(embed=embed)


class ImageGen(commands.GroupCog, name="imagine"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="generate", description="Generate an AI image using Pollinations.ai (free, no API key needed).")
    @app_commands.describe(prompt="Describe the image you want to create", model="Image model to use", width="Image width (default 1024)", height="Image height (default 1024)")
    @app_commands.choices(model=[
        app_commands.Choice(name="Flux (Best Quality)", value="flux"),
        app_commands.Choice(name="Flux Realism", value="flux-realism"),
        app_commands.Choice(name="Flux Anime", value="flux-anime"),
        app_commands.Choice(name="Flux 3D", value="flux-3d"),
        app_commands.Choice(name="Turbo (Fastest)", value="turbo"),
    ])
    @command_guard
    async def generate(self, interaction: discord.Interaction, prompt: str, model: str = "flux", width: int = 1024, height: int = 1024):
        await interaction.response.defer()
        import random
        width = max(256, min(1920, width))
        height = max(256, min(1920, height))
        seed = random.randint(1, 999999)
        encoded = urllib.parse.quote(prompt)
        image_url = f"https://image.pollinations.ai/prompt/{encoded}?width={width}&height={height}&seed={seed}&model={model}&nologo=true"
        embed = comprehensive_embed(
            title="🎨 AI Image Generated",
            description=f"**Prompt:** {prompt[:200]}",
            color=discord.Color.purple()
        )
        embed.add_field(name="Model", value=model.replace("-", " ").title(), inline=True)
        embed.add_field(name="Dimensions", value=f"{width}×{height}", inline=True)
        embed.add_field(name="Seed", value=str(seed), inline=True)
        embed.set_image(url=image_url)
        embed.set_footer(text="Powered by Pollinations.ai | XERO Bot")
        view = discord.ui.View()
        view.add_item(discord.ui.Button(label="Open Full Size", url=image_url, style=discord.ButtonStyle.link))
        await interaction.followup.send(embed=embed, view=view)

    @app_commands.command(name="variations", description="Generate 3 variations of an image with the same prompt.")
    @app_commands.describe(prompt="Image description")
    @command_guard
    async def variations(self, interaction: discord.Interaction, prompt: str):
        await interaction.response.defer()
        import random
        encoded = urllib.parse.quote(prompt)
        seeds = [random.randint(1, 999999) for _ in range(3)]
        embed = comprehensive_embed(title="🎨 Image Variations", description=f"**Prompt:** {prompt[:200]}", color=discord.Color.purple())
        for i, seed in enumerate(seeds, 1):
            url = f"https://image.pollinations.ai/prompt/{encoded}?width=512&height=512&seed={seed}&model=flux&nologo=true"
            embed.add_field(name=f"Variation {i}", value=f"[View Image]({url}) | Seed: {seed}", inline=True)
        embed.set_image(url=f"https://image.pollinations.ai/prompt/{encoded}?width=512&height=512&seed={seeds[0]}&model=flux&nologo=true")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="avatar-style", description="Reimagine a user's avatar in a different art style.")
    @app_commands.describe(user="User whose avatar to reimagine", style="Art style")
    @app_commands.choices(style=[
        app_commands.Choice(name="Anime", value="anime portrait"),
        app_commands.Choice(name="Oil Painting", value="oil painting portrait"),
        app_commands.Choice(name="Pixel Art", value="pixel art character"),
        app_commands.Choice(name="Watercolor", value="watercolor portrait"),
        app_commands.Choice(name="Cyberpunk", value="cyberpunk neon portrait"),
        app_commands.Choice(name="Sketch", value="pencil sketch portrait"),
    ])
    @command_guard
    async def avatar_style(self, interaction: discord.Interaction, user: discord.Member = None, style: str = "anime portrait"):
        await interaction.response.defer()
        import random
        target = user or interaction.user
        prompt = f"{style} of a Discord user named {target.display_name}, highly detailed, professional quality"
        encoded = urllib.parse.quote(prompt)
        seed = random.randint(1, 999999)
        image_url = f"https://image.pollinations.ai/prompt/{encoded}?width=512&height=512&seed={seed}&model=flux&nologo=true"
        embed = comprehensive_embed(
            title=f"🎨 {target.display_name} — {style.title()}",
            color=discord.Color.purple()
        )
        embed.set_image(url=image_url)
        embed.set_thumbnail(url=target.display_avatar.url)
        embed.set_footer(text="Powered by Pollinations.ai | XERO Bot")
        await interaction.followup.send(embed=embed)


async def setup(bot):
    await bot.add_cog(Profile(bot))
    await bot.add_cog(ImageGen(bot))
