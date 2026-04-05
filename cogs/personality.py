"""
XERO Bot — Personality & Voice System
XERO has a real character. It celebrates, reacts, gives witty responses,
announces milestones, and makes the server feel alive.
This is what makes people actually LIKE the bot vs just using it.
"""
import discord
from utils.guard import command_guard
from discord.ext import commands, tasks
from discord import app_commands
import logging
import random
import datetime
import aiosqlite
from utils.embeds import (
    success_embed, error_embed, info_embed, comprehensive_embed,
    milestone_embed, XERO, FOOTER_MAIN
)

logger = logging.getLogger("XERO.Personality")

# ── XERO's personality lines ──────────────────────────────────────────────────

SLOT_WIN_LINES = [
    "💰 Hold on... ARE THOSE CHERRIES?! *JACKPOT!* You're rich baby!",
    "🎰 The machine shook. The lights went crazy. Congratulations, you broke the casino.",
    "💎 Seven. Seven. SEVEN. Someone call security.",
    "🤑 I've never seen someone that lucky. Are you sure you're not cheating?",
    "🎊 BOOM! The crowd goes wild! Actually there's no crowd but I'm going wild for you!",
]

SLOT_LOSE_LINES = [
    "🎰 You spun. You lost. You stared at the screen. Happens to everyone.",
    "💸 Look on the bright side — at least you have the experience of losing money.",
    "😬 The slot machine looked at your wallet and then laughed. Try again?",
    "📉 Rough. But character-building! That's what I tell myself anyway.",
    "🪙 One more spin? That's what they ALL say...",
]

WELCOME_LINES = [
    "Look who showed up! {member} just walked in — give them a warm welcome! 👋",
    "ALERT: An incredible human just joined. {member}, we've been waiting for you. 🎉",
    "{member} has entered the server. XERO recognizes a legend when it sees one.",
    "The server just got better. Welcome, {member}! Don't let the normies scare you. 😄",
    "Rumor has it {member} is the most awesome person to ever join this server. Unverified, but I believe it.",
]

LEVEL_UP_LINES = [
    "👀 {member} just hit **Level {level}**. At this rate they'll own the whole server.",
    "⬆️ **Level {level}** unlocked for {member}. The grind is real.",
    "🔥 {member} is on FIRE — **Level {level}** achieved. Someone stop them.",
    "💪 {member} grinded their way to **Level {level}**. Respect.",
    "📈 The stats don't lie — {member} just hit **Level {level}** and I'm here for it.",
]

HEIST_SUCCESS_LINES = [
    "🏦 The crew pulled it off. The bank never saw it coming. Beautiful work.",
    "💰 Another successful job. XERO doesn't condone this. XERO is also impressed.",
    "🔫 The heist team walked in, walked out, and didn't look back. Legendary.",
]

BOT_STATUS_LINES = [
    "👁️ watching over {guilds} servers",
    "🛡️ protecting {users} members",
    "🤖 running 250+ commands",
    "💎 your premium bot, for free",
    "⚡ powered by NVIDIA AI",
]

# Milestone member counts to celebrate
MEMBER_MILESTONES = [10, 25, 50, 100, 250, 500, 1000, 2500, 5000, 10000]


class Personality(commands.Cog):
    def __init__(self, bot):
        self.bot = bot
        self.rotate_status.start()

    def cog_unload(self):
        self.rotate_status.cancel()

    # ── Background: Rotate status ──────────────────────────────────────────
    @tasks.loop(minutes=10)
    async def rotate_status(self):
        try:
            line = random.choice(BOT_STATUS_LINES)
            text = line.format(
                guilds=len(self.bot.guilds),
                users=sum(g.member_count for g in self.bot.guilds)
            )
            await self.bot.change_presence(
                activity=discord.Activity(
                    type=discord.ActivityType.watching,
                    name=text
                )
            )
        except Exception as e:
            logger.error(f"Status rotation error: {e}")

    @rotate_status.before_loop
    async def before_status(self):
        await self.bot.wait_until_ready()

    # ── Called by events.py on member join ────────────────────────────────
    async def on_member_welcome(self, member: discord.Member, channel: discord.TextChannel):
        """Send a witty welcome line alongside the embed."""
        # Feature disabled as per user request to reduce noise
        pass

    # ── Called by events.py on level up ───────────────────────────────────
    async def on_level_up(self, member: discord.Member, level: int, channel: discord.TextChannel):
        """Add a witty line to level-up announcements."""
        # Feature disabled as per user request to reduce noise
        pass

    # ── Called by economy after slot result ───────────────────────────────
    async def get_slot_comment(self, won: bool) -> str:
        lines = SLOT_WIN_LINES if won else SLOT_LOSE_LINES
        return random.choice(lines)

    # ── Check member milestones on join ───────────────────────────────────
    async def check_milestone(self, guild: discord.Guild):
        count = guild.member_count
        if count not in MEMBER_MILESTONES:
            return

        # Avoid re-announcing same milestone
        async with self.bot.db._db_context() as db:
            async with db.execute(
                "SELECT last_fired FROM personality_log WHERE guild_id=? AND event_type=?",
                (guild.id, f"milestone_{count}")
            ) as c:
                row = await c.fetchone()
            if row:
                return  # Already fired
            await db.execute(
                "INSERT OR REPLACE INTO personality_log (guild_id, event_type) VALUES (?,?)",
                (guild.id, f"milestone_{count}")
            )
            await db.commit()

        settings = await self.bot.db.get_guild_settings(guild.id)
        channel_id = settings.get("milestone_channel_id") or settings.get("welcome_channel_id")
        if not channel_id:
            return
        ch = guild.get_channel(channel_id)
        if not ch:
            return

        embed = milestone_embed(guild, count)
        try:
            await ch.send(content="@everyone", embed=embed)
        except Exception:
            try:
                await ch.send(embed=embed)
            except Exception:
                pass
        logger.info(f"🎊 Milestone {count} celebrated in {guild.name}")

    # ── /xero quote ────────────────────────────────────────────────────────
    @app_commands.command(name="xero", description="Get a random XERO personality quote — motivational, funny, or just chaotic.")
    @app_commands.choices(mood=[
        app_commands.Choice(name="🔥 Hype Me Up", value="hype"),
        app_commands.Choice(name="😂 Make Me Laugh", value="funny"),
        app_commands.Choice(name="🧠 Drop Some Wisdom", value="wisdom"),
        app_commands.Choice(name="🌙 Be Philosophical", value="philosophical"),
        app_commands.Choice(name="🎲 Random", value="random"),
    ])
    @command_guard
    async def xero_quote(self, interaction: discord.Interaction, mood: str = "random"):
        await interaction.response.defer()
        mood_prompts = {
            "hype":          "Give an extremely hype, energy-filled motivational message. Short, punchy, under 100 words.",
            "funny":         "Give a genuinely funny, witty one-liner or short joke. Actually funny, not forced.",
            "wisdom":        "Share a single piece of profound, practical wisdom in under 80 words.",
            "philosophical": "Say something thought-provoking and philosophical. Short but deep.",
            "random":        "Say whatever you feel like — witty, weird, wise, or wacky. Be authentic.",
        }
        system = (
            "You are XERO, an AI Discord bot with a sharp, witty, confident personality. "
            "You're smart but not pretentious. Direct but not rude. "
            "You speak like a wise friend who happens to be incredibly capable. "
            "You're proud of being free while others charge. "
            "Never use generic corporate-speak. Be real."
        )
        response = await self.bot.nvidia.ask(mood_prompts[mood], system)
        if not response:
            response = "XERO is momentarily speechless. First time for everything."

        embed = discord.Embed(
            description=f"*\"{response}\"*\n\n— **XERO**",
            color=XERO.SECONDARY
        )
        embed.set_author(
            name="XERO",
            icon_url=self.bot.user.display_avatar.url
        )
        embed.set_footer(text=f"Requested by {interaction.user.display_name}  •  XERO Bot")
        await interaction.followup.send(embed=embed)

    # ── /vibe-check ────────────────────────────────────────────────────────
    @app_commands.command(name="vibe-check", description="XERO reads the last 30 messages in this channel and gives its honest take.")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def vibe_check(self, interaction: discord.Interaction):
        await interaction.response.defer()
        messages = []
        async for msg in interaction.channel.history(limit=30):
            if not msg.author.bot and msg.content:
                messages.append(f"{msg.author.display_name}: {msg.content[:100]}")
        if not messages:
            return await interaction.followup.send(embed=info_embed("No Messages", "No recent messages to analyze."))

        context = "\n".join(reversed(messages))
        prompt = (
            f"Read these recent Discord messages and give a short, honest, witty vibe check. "
            f"What's the mood? What's going on? Any drama? Any chaos? Be real, keep it under 100 words.\n\n"
            f"Messages:\n{context}"
        )
        system = (
            "You are XERO, a witty AI bot. You're giving an honest, funny vibe check of a Discord channel. "
            "Be observational, direct, and entertaining. Don't be mean, but don't sugarcoat. "
            "Speak like a cool friend commenting on the group chat."
        )
        response = await self.bot.nvidia.ask(prompt, system)
        embed = discord.Embed(
            title=f"📡  Vibe Check — #{interaction.channel.name}",
            description=response or "Vibes: immeasurable. My day: ruined.",
            color=XERO.SECONDARY
        )
        embed.set_footer(text="XERO Personality Engine  •  Honest takes only")
        await interaction.followup.send(embed=embed)

    # ── /roast-server ──────────────────────────────────────────────────────
    @app_commands.command(name="roast-server", description="XERO gives this server a playful roast based on its stats and setup.")
    @app_commands.checks.has_permissions(manage_guild=True)
    @command_guard
    async def roast_server(self, interaction: discord.Interaction):
        await interaction.response.defer()
        guild = interaction.guild
        settings = await self.bot.db.get_guild_settings(guild.id)
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT SUM(commands_used) FROM user_stats WHERE guild_id=?", (guild.id,)) as c:
                cmds = (await c.fetchone())[0] or 0

        bots    = sum(1 for m in guild.members if m.bot)
        humans  = guild.member_count - bots
        channels = len(guild.channels)
        roles    = len(guild.roles)
        has_welcome = bool(settings.get("welcome_channel_id"))
        has_logs    = bool(settings.get("log_channel_id"))

        prompt = (
            f"Roast this Discord server in a funny, playful way based on these stats. "
            f"Keep it light — funny but not mean. 2-3 sentences max.\n\n"
            f"Server: {guild.name}\n"
            f"Members: {guild.member_count} ({humans} humans, {bots} bots)\n"
            f"Channels: {channels}\nRoles: {roles}\n"
            f"Commands used: {cmds:,}\n"
            f"Welcome channel: {'yes' if has_welcome else 'no'}\n"
            f"Log channel: {'yes' if has_logs else 'no'}\n"
            f"Boost level: {guild.premium_tier}"
        )
        system = (
            "You are XERO, giving a playful server roast. Be witty and specific to the data. "
            "Punchy, funny, not mean. 2-3 sentences only."
        )
        response = await self.bot.nvidia.ask(prompt, system)
        embed = discord.Embed(
            title=f"🔥  Server Roast — {guild.name}",
            description=response or "This server is so average XERO couldn't even think of a roast.",
            color=XERO.FUN if hasattr(XERO, "FUN") else XERO.MOD
        )
        embed.set_thumbnail(url=guild.icon.url if guild.icon else None)
        embed.set_footer(text="XERO Personality Engine  •  Don't take it personally")
        await interaction.followup.send(embed=embed)

    # ── /milestone-set ─────────────────────────────────────────────────────
    @app_commands.command(name="milestone-channel", description="Set the channel where XERO announces server member milestones.")
    @app_commands.describe(channel="Channel for milestone announcements")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def milestone_channel(self, interaction: discord.Interaction, channel: discord.TextChannel):
        await self.bot.db.update_guild_setting(interaction.guild.id, "milestone_channel_id", channel.id)
        next_m = next((m for m in MEMBER_MILESTONES if m > interaction.guild.member_count), None)
        await interaction.response.send_message(embed=success_embed(
            "Milestone Channel Set",
            f"Member milestones will be announced in {channel.mention}.\n\n"
            f"**Current members:** {interaction.guild.member_count:,}\n"
            f"**Next milestone:** {next_m:,} members" + (f" — just {next_m - interaction.guild.member_count} away!" if next_m else "")
        ))

    # ── /personality-toggle ────────────────────────────────────────────────
    @app_commands.command(name="personality-toggle", description="Enable or disable XERO's personality responses (welcome lines, level-up comments, etc.).")
    @app_commands.describe(enabled="Enable or disable personality features")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def personality_toggle(self, interaction: discord.Interaction, enabled: bool = True):
        await self.bot.db.update_guild_setting(interaction.guild.id, "personality_enabled", 1 if enabled else 0)
        if enabled:
            await interaction.response.send_message(embed=success_embed(
                "Personality Enabled",
                "XERO will now add witty comments to welcome messages, level-ups, slot results, and milestones.\n"
                "*Making your server feel alive, one comment at a time.*"
            ))
        else:
            await interaction.response.send_message(embed=info_embed(
                "Personality Disabled",
                "XERO will stick to clean, professional responses. No personality extras.\n"
                "*Boring, but valid.*"
            ))


async def setup(bot):
    await bot.add_cog(Personality(bot))
