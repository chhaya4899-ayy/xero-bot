"""XERO Bot — Advanced AI Features (8 commands) — AI Debate, RPG, Advisor, Coach"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging
import asyncio
from utils.embeds import comprehensive_embed, success_embed, error_embed, info_embed

logger = logging.getLogger("XERO.AIAdvanced")

# RPG game state per user: user_id -> game_state dict
RPG_GAMES: dict = {}


class AIAdvanced(commands.GroupCog, name="nexus"):
    def __init__(self, bot):
        self.bot = bot

    # ── AI Debate ─────────────────────────────────────────────────────────
    @app_commands.command(name="debate", description="Watch two AI personas argue both sides of any topic live in chat.")
    @app_commands.describe(topic="Topic to debate", rounds="Number of debate rounds (1-4)")
    @command_guard
    async def debate(self, interaction: discord.Interaction, topic: str, rounds: int = 2):
        await interaction.response.defer()
        rounds = max(1, min(4, rounds))

        intro_embed = comprehensive_embed(
            title=f"⚔️ AI Debate: {topic[:60]}",
            description=f"**{rounds} round(s)** | Two AI personas will argue opposing sides.\n\nPreparing arguments...",
            color=discord.Color.red()
        )
        await interaction.followup.send(embed=intro_embed)

        system_pro = (
            f"You are debating IN FAVOR of: '{topic}'. "
            "Give a compelling, detailed argument supporting this position. "
            "Be specific, use examples, and directly counter any previous opposing arguments. "
            "Keep your response to 2-3 focused paragraphs. Use Discord markdown."
        )
        system_con = (
            f"You are debating AGAINST: '{topic}'. "
            "Give a compelling, detailed argument opposing this position. "
            "Be specific, use examples, and directly counter any previous pro arguments. "
            "Keep your response to 2-3 focused paragraphs. Use Discord markdown."
        )

        pro_history = []
        con_history = []

        for round_num in range(1, rounds + 1):
            # PRO side
            pro_prompt = f"Round {round_num}. " + (f"Counter the opponent's last argument and advance your case." if round_num > 1 else "Open the debate with your strongest argument.")
            pro_response = await self.bot.nvidia.ask(pro_prompt, system_pro)
            pro_history.append(pro_response)
            con_history.append(pro_response)  # Give con side context

            pro_embed = discord.Embed(
                title=f"🟢 FOR — Round {round_num}",
                description=pro_response[:2048] if pro_response else "No response.",
                color=discord.Color.green()
            )
            pro_embed.set_footer(text=f"⚔️ Debate: {topic[:40]} | Round {round_num}/{rounds}")
            await interaction.channel.send(embed=pro_embed)
            await asyncio.sleep(1)

            # CON side
            con_prompt = f"Round {round_num}. Counter: '{pro_response[:300]}'. Advance your case."
            con_response = await self.bot.nvidia.ask(con_prompt, system_con)

            con_embed = discord.Embed(
                title=f"🔴 AGAINST — Round {round_num}",
                description=con_response[:2048] if con_response else "No response.",
                color=discord.Color.red()
            )
            con_embed.set_footer(text=f"⚔️ Debate: {topic[:40]} | Round {round_num}/{rounds}")
            await interaction.channel.send(embed=con_embed)
            await asyncio.sleep(1)

        # AI verdict
        verdict_prompt = (
            f"You just watched a {rounds}-round debate on: '{topic}'.\n"
            f"FOR side said: {' | '.join(pro_history)[:500]}\n"
            f"AGAINST side said: {' | '.join([con_response or ''])[:500]}\n"
            "Give a balanced, thoughtful verdict: who made stronger arguments and why? "
            "Also summarize the core disagreement in 1-2 sentences."
        )
        verdict = await self.bot.nvidia.ask(verdict_prompt)
        verdict_embed = comprehensive_embed(
            title="⚖️ Debate Verdict",
            description=verdict[:2048] if verdict else "No verdict available.",
            color=discord.Color.gold()
        )
        verdict_embed.set_footer(text=f"Topic: {topic[:60]} | XERO AI Debate")
        await interaction.channel.send(embed=verdict_embed)

    # ── AI RPG Dungeon ────────────────────────────────────────────────────
    @app_commands.command(name="rpg-start", description="Start an AI-powered text RPG adventure. Your choices shape the story.")
    @app_commands.describe(character_name="Your character's name", character_class="Your class/role", setting="World/setting for your adventure")
    @app_commands.choices(character_class=[
        app_commands.Choice(name="⚔️ Warrior", value="Warrior"),
        app_commands.Choice(name="🧙 Mage", value="Mage"),
        app_commands.Choice(name="🏹 Ranger", value="Ranger"),
        app_commands.Choice(name="🗡️ Rogue", value="Rogue"),
        app_commands.Choice(name="🛡️ Paladin", value="Paladin"),
    ])
    @command_guard
    async def rpg_start(self, interaction: discord.Interaction, character_name: str, character_class: str = "Warrior", setting: str = "a dark fantasy realm"):
        await interaction.response.defer()
        uid = interaction.user.id
        # Initialize game state
        RPG_GAMES[uid] = {
            "name": character_name,
            "class": character_class,
            "setting": setting,
            "hp": 100,
            "gold": 10,
            "inventory": ["Rusty Sword" if character_class == "Warrior" else "Staff" if character_class == "Mage" else "Bow"],
            "history": [],
            "chapter": 1,
        }
        system = (
            f"You are the game master of an immersive text RPG. "
            f"The player is '{character_name}', a {character_class} in {setting}. "
            f"Create a vivid, engaging opening scene with a clear situation. "
            f"End EVERY response with exactly 3 numbered choices the player can make. "
            f"Format: '**What do you do?**\n1. [Action]\n2. [Action]\n3. [Action]' "
            f"Keep responses under 400 words. Track HP ({RPG_GAMES[uid]['hp']}), gold ({RPG_GAMES[uid]['gold']}), inventory."
        )
        response = await self.bot.nvidia.ask(f"Begin the adventure for {character_name} the {character_class}.", system)
        RPG_GAMES[uid]["history"].append({"role": "assistant", "content": response or ""})
        embed = discord.Embed(
            title=f"⚔️ {character_name}'s Adventure Begins — Chapter 1",
            description=response[:2048] if response else "Your adventure begins...",
            color=discord.Color.dark_purple()
        )
        embed.add_field(name="❤️ HP", value="100/100", inline=True)
        embed.add_field(name="💰 Gold", value="10", inline=True)
        embed.add_field(name="🎒 Inventory", value=RPG_GAMES[uid]["inventory"][0], inline=True)
        embed.set_footer(text=f"Use /nexus rpg-action to choose your action | {character_class} in {setting}")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="rpg-action", description="Make a choice in your RPG adventure.")
    @app_commands.describe(action="What you do (type a number 1-3 or describe your action)")
    @command_guard
    async def rpg_action(self, interaction: discord.Interaction, action: str):
        await interaction.response.defer()
        uid = interaction.user.id
        if uid not in RPG_GAMES:
            return await interaction.followup.send(embed=error_embed("No Active Game", "Start a game with `/nexus rpg-start`!"), ephemeral=True)
        game = RPG_GAMES[uid]
        game["chapter"] += 1
        system = (
            f"You are the game master of a text RPG. "
            f"Player: '{game['name']}' the {game['class']}. HP: {game['hp']}/100. Gold: {game['gold']}. "
            f"Inventory: {', '.join(game['inventory'])}. Chapter: {game['chapter']}. "
            f"Continue the story based on their action. Make consequences feel real. "
            f"Occasionally add combat (reduce HP), rewards (add gold/items), or story twists. "
            f"End with 3 numbered choices. Under 400 words."
        )
        full_prompt = "\n".join([h["content"] for h in game["history"][-4:]]) + f"\n\nPlayer action: {action}"
        response = await self.bot.nvidia.ask(full_prompt, system)
        if response:
            game["history"].append({"role": "user", "content": action})
            game["history"].append({"role": "assistant", "content": response})
        embed = discord.Embed(
            title=f"⚔️ {game['name']}'s Adventure — Chapter {game['chapter']}",
            description=response[:2048] if response else "The story continues...",
            color=discord.Color.dark_purple()
        )
        embed.add_field(name="❤️ HP", value=f"{game['hp']}/100", inline=True)
        embed.add_field(name="💰 Gold", value=str(game["gold"]), inline=True)
        embed.add_field(name="🎒 Items", value=", ".join(game["inventory"][:3]) or "None", inline=True)
        embed.set_footer(text=f"Chapter {game['chapter']} | /nexus rpg-action to continue")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="rpg-quit", description="End your current RPG adventure.")
    async def rpg_quit(self, interaction: discord.Interaction):
        uid = interaction.user.id
        if uid not in RPG_GAMES:
            return await interaction.response.send_message(embed=error_embed("No Active Game", "You don't have an active RPG game."), ephemeral=True)
        game = RPG_GAMES.pop(uid)
        await interaction.response.send_message(embed=info_embed(
            f"Adventure Ended ⚔️",
            f"**{game['name']}** the {game['class']} adventured for **{game['chapter']}** chapters.\n"
            f"**Final HP:** {game['hp']}/100 | **Gold:** {game['gold']} | **Items:** {len(game['inventory'])}"
        ))

    # ── AI Mod Advisor ────────────────────────────────────────────────────
    @app_commands.command(name="mod-advice", description="Get AI-powered moderation advice for a user's case history.")
    @app_commands.describe(user="User to analyze")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def mod_advice(self, interaction: discord.Interaction, user: discord.Member):
        await interaction.response.defer(ephemeral=True)
        cases = await self.bot.db.get_mod_cases(interaction.guild.id, user.id, limit=10)
        warns = await self.bot.db.get_warnings(interaction.guild.id, user.id)
        if not cases and not warns:
            return await interaction.followup.send(embed=info_embed("Clean Record", f"{user.mention} has no moderation history. No action needed."))

        case_summary = "\n".join([f"- {c['action'].upper()}: {c['reason']} ({c['timestamp'][:10]})" for c in cases[:8]])
        warn_count = len(warns)
        prompt = (
            f"As a moderation AI, analyze this Discord user's history and recommend the appropriate next action.\n\n"
            f"User: {user.display_name} | Account age: {(discord.utils.utcnow() - user.created_at).days} days | "
            f"Server join: {(discord.utils.utcnow() - user.joined_at).days} days ago\n\n"
            f"Warning count: {warn_count}\n"
            f"Case history:\n{case_summary or 'No formal cases'}\n\n"
            f"Based on this pattern, provide:\n"
            f"1. Risk assessment (low/medium/high)\n"
            f"2. Recommended action and why\n"
            f"3. Whether escalation is needed\n"
            f"4. Any patterns you notice\n"
            f"Be specific and actionable."
        )
        response = await self.bot.nvidia.ask(prompt)
        embed = comprehensive_embed(
            title=f"🤖 AI Mod Advisor — {user.display_name}",
            description=response[:2048] if response else "Could not generate advice.",
            color=discord.Color.orange()
        )
        embed.add_field(name="Cases", value=str(len(cases)), inline=True)
        embed.add_field(name="Warnings", value=str(warn_count), inline=True)
        embed.set_thumbnail(url=user.display_avatar.url)
        embed.set_footer(text="AI advice is a suggestion — always use your own judgment.")
        await interaction.followup.send(embed=embed)

    # ── AI Communication Coach ────────────────────────────────────────────
    @app_commands.command(name="coach", description="Get AI feedback on your writing — tone, clarity, impact, and improvement tips.")
    @app_commands.describe(text="The text you want analyzed and improved")
    @command_guard
    async def coach(self, interaction: discord.Interaction, text: str):
        await interaction.response.defer()
        prompt = (
            f"Analyze this text as a professional communication coach:\n\n\"{text}\"\n\n"
            f"Provide a detailed analysis covering:\n"
            f"**1. Tone** — What emotion/attitude does it convey?\n"
            f"**2. Clarity** — Is the message clear? Any ambiguity?\n"
            f"**3. Impact** — How will the reader likely perceive this?\n"
            f"**4. Strengths** — What works well?\n"
            f"**5. Improvements** — Specific suggestions with examples\n"
            f"**6. Rewritten version** — Show how it could be better\n\n"
            f"Be specific, constructive, and practical."
        )
        response = await self.bot.nvidia.ask(prompt)
        embed = comprehensive_embed(
            title="🗣️ Communication Coach Analysis",
            description=response[:2048] if response else "Analysis failed.",
            color=discord.Color.teal()
        )
        embed.add_field(name="Your Text", value=text[:400], inline=False)
        embed.set_footer(text="XERO AI Communication Coach | Powered by NVIDIA Llama 4")
        await interaction.followup.send(embed=embed)

    # ── AI Explainer ──────────────────────────────────────────────────────
    @app_commands.command(name="explain", description="Get an ELI5 or expert-level explanation of any concept.")
    @app_commands.describe(concept="What to explain", level="Explanation depth")
    @app_commands.choices(level=[
        app_commands.Choice(name="ELI5 (5-year-old)", value="eli5"),
        app_commands.Choice(name="Simple", value="simple"),
        app_commands.Choice(name="Detailed", value="detailed"),
        app_commands.Choice(name="Expert / Technical", value="expert"),
    ])
    @command_guard
    async def explain(self, interaction: discord.Interaction, concept: str, level: str = "simple"):
        await interaction.response.defer()
        level_prompts = {
            "eli5": "Explain this like I'm 5 years old, using simple words and a fun analogy:",
            "simple": "Explain this clearly and simply for a general audience:",
            "detailed": "Give a comprehensive, detailed explanation with examples, context, and key concepts:",
            "expert": "Give a technical, expert-level explanation with depth, nuance, and advanced concepts:",
        }
        prompt = f"{level_prompts[level]} {concept}"
        response = await self.bot.nvidia.ask(prompt)
        embed = comprehensive_embed(
            title=f"💡 Explanation: {concept[:50]}",
            description=response[:2048] if response else "Could not generate explanation.",
            color=discord.Color.blurple()
        )
        embed.add_field(name="Level", value=level.upper(), inline=True)
        embed.set_footer(text="XERO AI Explainer | Powered by NVIDIA Llama 4")
        await interaction.followup.send(embed=embed)


async def setup(bot):
    await bot.add_cog(AIAdvanced(bot))
