"""
XERO Bot — Help System
Interactive paginated help with category dropdowns.
Surpasses MEE6, Carl-bot, and Unbelievaboat's help systems.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
from utils.embeds import comprehensive_embed, info_embed, XERO, FOOTER_MAIN

logger = logging.getLogger("XERO.Help")

# ── Category definitions ──────────────────────────────────────────────────────

CATEGORIES = {
    "🤖 AI": {
        "description": "AI-powered commands powered by NVIDIA Llama 4 Maverick",
        "commands": [
            ("/ai ask", "Ask the AI any question"),
            ("/ai chat", "Context-aware conversation with memory"),
            ("/ai summarize", "Summarize text or recent chat"),
            ("/ai translate", "Translate to any language"),
            ("/ai brainstorm", "Generate ideas on any topic"),
            ("/ai code-explain", "Get detailed code explanations"),
            ("/ai code-debug", "Debug code and get fixes"),
            ("/ai grammar", "Check grammar and spelling"),
            ("/ai rewrite", "Rewrite text in any style"),
            ("/ai fact-check", "AI fact-check any claim"),
            ("/ai roast", "Generate a playful roast"),
            ("/ai imagine", "Generate AI images (FLUX AI)"),
            ("/ai analyze-image", "Analyze any image with AI vision"),
            ("/ai persona", "Change the AI personality for this server"),
            ("/ai clear-memory", "Clear AI conversation history"),
        ]
    },
    "🛡️ Moderation": {
        "description": "Advanced moderation tools that surpass every other bot",
        "commands": [
            ("/mod ban", "Ban a member with reason and duration"),
            ("/mod unban", "Unban a user by ID"),
            ("/mod kick", "Kick a member from the server"),
            ("/mod mute", "Timeout a member"),
            ("/mod warn", "Issue a formal warning"),
            ("/mod warnings", "View a member's warnings"),
            ("/mod clear-warnings", "Clear a member's warnings"),
            ("/mod purge", "Bulk delete messages"),
            ("/mod history", "View moderation history"),
            ("/mod case", "View a specific mod case"),
            ("/mod lock", "Lock a channel"),
            ("/mod unlock", "Unlock a channel"),
            ("/mod slowmode", "Set channel slowmode"),
            ("/mod nick", "Change a member's nickname"),
            ("/mod move", "Move a member to another voice channel"),
        ]
    },
    "⚔️ AutoMod": {
        "description": "Aegis Neural AutoMod — 8-rule real-time enforcement engine",
        "commands": [
            ("/automod enable", "Enable the automod system"),
            ("/automod disable", "Disable the automod system"),
            ("/automod config", "View current automod config"),
            ("/automod anti-spam", "Configure spam protection"),
            ("/automod anti-caps", "Configure caps filter"),
            ("/automod anti-links", "Configure link filter"),
            ("/automod anti-invites", "Configure invite filter"),
            ("/automod anti-mentions", "Configure mass mention protection"),
            ("/automod anti-profanity", "Configure word filter"),
            ("/automod log-channel", "Set the automod log channel"),
            ("/automod add-word", "Add word to the filter"),
            ("/automod remove-word", "Remove word from the filter"),
            ("/automod list-words", "List all filtered words"),
            ("/automod whitelist", "Whitelist a channel from automod"),
            ("/automod strikes", "Configure strike thresholds"),
        ]
    },
    "📊 Levels": {
        "description": "XP & leveling system — beats MEE6 in every way",
        "commands": [
            ("/rank", "View your rank card and XP progress"),
            ("/leaderboard", "View the XP leaderboard"),
            ("/rank-config", "Configure level-up notifications"),
            ("/level-reward add", "Add a role reward for reaching a level"),
            ("/level-reward remove", "Remove a level reward"),
            ("/level-reward list", "View all level rewards"),
            ("/level reset", "Reset a user's XP (admin)"),
            ("/level set", "Set a user's XP manually (admin)"),
        ]
    },
    "💰 Economy": {
        "description": "Full featured economy with stocks, heists, crafting and more",
        "commands": [
            ("/balance", "Check your wallet and bank balance"),
            ("/daily", "Claim your daily reward"),
            ("/work", "Earn coins by working"),
            ("/deposit", "Deposit coins to your bank"),
            ("/withdraw", "Withdraw coins from bank"),
            ("/pay", "Send coins to another member"),
            ("/rob", "Attempt to rob another member"),
            ("/shop", "Browse the server shop"),
            ("/buy", "Purchase an item from the shop"),
            ("/inventory", "View your inventory"),
            ("/leaderboard-eco", "Economy richest leaderboard"),
            ("/heist", "Start a group bank heist"),
            ("/stocks", "View the XERO stock exchange"),
            ("/buy-stock", "Buy shares of a stock"),
            ("/sell-stock", "Sell your stock shares"),
            ("/portfolio", "View your stock portfolio"),
            ("/craft", "Combine items to craft new ones"),
            ("/event", "Check the current economy event"),
        ]
    },
    "🎉 Fun": {
        "description": "Fun commands to keep your community entertained",
        "commands": [
            ("/coinflip", "Flip a coin"),
            ("/roll", "Roll dice (e.g. 2d6)"),
            ("/8ball", "Ask the magic 8-ball"),
            ("/would-you-rather", "Random would you rather question"),
            ("/trivia", "Answer a trivia question"),
            ("/meme", "Get a random meme"),
            ("/joke", "Get a random joke"),
            ("/riddle", "Get a riddle with answer"),
            ("/choose", "Make XERO choose between options"),
            ("/rate", "Rate something out of 10"),
            ("/slots", "Play the slot machine"),
            ("/pp", "Check someone's pp size"),
            ("/ship", "Ship two users together"),
        ]
    },
    "ℹ️ Info": {
        "description": "Detailed info commands for users, servers, roles, and more",
        "commands": [
            ("/info user", "Detailed user profile with level, economy, mod history"),
            ("/info server", "Full server statistics and info"),
            ("/info role", "Detailed role information"),
            ("/info channel", "Channel statistics and details"),
            ("/info bot", "XERO bot info and system stats"),
            ("/info emoji", "Emoji details and usage"),
            ("/info invite", "View server invites"),
            ("/info perms", "Check a user's permissions"),
        ]
    },
    "🎫 Tickets": {
        "description": "Full ticket system with categories and transcripts",
        "commands": [
            ("/ticket setup", "Set up the ticket system"),
            ("/ticket panel", "Post the ticket creation panel"),
            ("/ticket close", "Close an open ticket"),
            ("/ticket add", "Add a member to a ticket"),
            ("/ticket remove", "Remove a member from a ticket"),
            ("/ticket claim", "Claim a ticket as staff"),
            ("/ticket rename", "Rename a ticket channel"),
            ("/ticket transcript", "Export ticket transcript"),
        ]
    },
    "🎊 Giveaways": {
        "description": "Full-featured giveaway system",
        "commands": [
            ("/giveaway start", "Start a giveaway"),
            ("/giveaway end", "End a giveaway early"),
            ("/giveaway reroll", "Reroll a giveaway winner"),
            ("/giveaway list", "List active giveaways"),
            ("/giveaway delete", "Delete a giveaway"),
        ]
    },
    "⚙️ Setup": {
        "description": "Server configuration and setup commands",
        "commands": [
            ("/setup welcome", "Configure welcome messages"),
            ("/setup farewell", "Configure farewell messages"),
            ("/setup autorole", "Set the auto-role for new members"),
            ("/setup log-channel", "Set the moderation log channel"),
            ("/setup mute-role", "Set the mute role"),
            ("/verify setup", "Set up member verification"),
            ("/verify panel", "Post the verification panel"),
            ("/verify method", "Configure verification methods"),
            ("/automod enable", "Enable the automod system"),
        ]
    },
    "🌟 Features": {
        "description": "Premium server features — all free with XERO",
        "commands": [
            ("/features stats-channel", "Auto-updating member count channels"),
            ("/features bump-reminder", "Automated bump reminders"),
            ("/features double-xp", "Start a double XP event"),
            ("/features weekly-reward", "Configure weekly reward"),
            ("/features message-log", "Toggle message logging"),
            ("/features voice-log", "Toggle voice event logging"),
            ("/birthday set", "Set your birthday"),
            ("/birthday list", "View upcoming birthdays"),
            ("/suggestions", "Submit a suggestion"),
            ("/starboard setup", "Set up the starboard"),
        ]
    },
}


# ── Help dropdown ─────────────────────────────────────────────────────────────

class CategorySelect(discord.ui.Select):
    def __init__(self):
        options = [
            discord.SelectOption(
                label=cat_name.split(" ", 1)[-1],
                description=data["description"][:100],
                emoji=cat_name.split(" ", 1)[0],
                value=cat_name
            )
            for cat_name, data in CATEGORIES.items()
        ]
        super().__init__(placeholder="Select a category...", options=options[:25])

    async def callback(self, interaction: discord.Interaction):
        cat = self.values[0]
        data = CATEGORIES[cat]
        embed = discord.Embed(
            title=f"{cat}",
            description=data["description"],
            color=XERO.PRIMARY
        )
        cmds = data["commands"]
        # Split into columns of 10
        col1 = cmds[:10]
        col2 = cmds[10:] if len(cmds) > 10 else []

        col1_text = "\n".join(f"`{c[0]}` — {c[1]}" for c in col1)
        embed.add_field(name="Commands", value=col1_text or "*None*", inline=False)

        if col2:
            col2_text = "\n".join(f"`{c[0]}` — {c[1]}" for c in col2)
            embed.add_field(name="More Commands", value=col2_text, inline=False)

        embed.set_footer(text=FOOTER_MAIN)
        await interaction.response.edit_message(embed=embed, view=self.view)


class HelpView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=300)
        self.add_item(CategorySelect())

    @discord.ui.button(label="Home", style=discord.ButtonStyle.secondary, emoji="🏠")
    async def home(self, interaction: discord.Interaction, button: discord.ui.Button):
        embed = build_home_embed()
        await interaction.response.edit_message(embed=embed, view=self)


# ── Embed builders ────────────────────────────────────────────────────────────

def build_home_embed() -> discord.Embed:
    embed = discord.Embed(
        title="XERO Bot — Command Help",
        description=(
            "XERO is the most advanced, fully free Discord bot.\n"
            "**300+ commands** across every feature area.\n\n"
            "Use the dropdown below to browse command categories."
        ),
        color=XERO.PRIMARY
    )

    # Quick stats
    total_cmds = sum(len(d["commands"]) for d in CATEGORIES.values())
    cats = list(CATEGORIES.keys())
    mid = len(cats) // 2
    col1 = "\n".join(f"{c}" for c in cats[:mid])
    col2 = "\n".join(f"{c}" for c in cats[mid:])
    embed.add_field(name="Categories", value=col1, inline=True)
    embed.add_field(name="\u200b", value=col2, inline=True)
    embed.add_field(name="📊 Stats", value=f"**{total_cmds}+** listed commands", inline=False)
    embed.set_footer(text=f"{FOOTER_MAIN}  •  Select a category below")
    return embed


# ── Cog ──────────────────────────────────────────────────────────────────────

class Help(commands.Cog):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="help", description="Browse all XERO commands by category.")
    async def help(self, interaction: discord.Interaction):
        embed = build_home_embed()
        view = HelpView()
        await interaction.response.send_message(embed=embed, view=view, ephemeral=True)

    @app_commands.command(name="commands", description="Quick overview of all XERO command categories.")
    async def commands_list(self, interaction: discord.Interaction):
        lines = []
        for cat, data in CATEGORIES.items():
            count = len(data["commands"])
            lines.append(f"{cat} — **{count} commands**")

        embed = discord.Embed(
            title="📋  XERO Command Categories",
            description="\n".join(lines) + "\n\n*Use `/help` to browse commands interactively.*",
            color=XERO.PRIMARY
        )
        embed.set_footer(text=FOOTER_MAIN)
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(Help(bot))
