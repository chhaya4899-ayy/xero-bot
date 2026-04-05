"""XERO Bot — Fun Commands (22 commands) — All AI-powered. Every response unique."""
import discord, random, aiohttp, asyncio, datetime, aiosqlite
from discord.ext import commands
from discord import app_commands
from utils.embeds import comprehensive_embed, info_embed, error_embed, success_embed, XERO
import logging
logger = logging.getLogger("XERO.Fun")

TRIVIA_SCORES: dict = {}
TRIVIA_ACTIVE: dict = {}


class Fun(commands.GroupCog, name="fun"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="8ball", description="Ask the AI magic 8-ball. Real answer based on your actual question.")
    @app_commands.describe(question="Your yes/no question")
    async def eight_ball(self, interaction: discord.Interaction, question: str):
        await interaction.response.defer()
        prompt = (
            f"You are a mystical 8-ball oracle. The user asked: \"{question}\"\n"
            f"Give a SHORT, cryptic, dramatic 8-ball style answer (1-2 sentences). "
            f"Be creative. Vary between positive, uncertain, and negative responses. "
            f"Start with: 'The stars say...', 'My visions reveal...', 'Fate declares...', or 'The oracle sees...'"
        )
        try: answer = await self.bot.nvidia.ask(prompt)
        except Exception: answer = random.choice(["It is certain.", "Very doubtful.", "Ask again later.", "Without a doubt."])
        embed = discord.Embed(color=XERO.PRIMARY)
        embed.set_author(name="🎱 Magic 8-Ball")
        embed.add_field(name="❓ Question", value=question,         inline=False)
        embed.add_field(name="🔮 Answer",   value=f"*{answer}*",   inline=False)
        embed.set_footer(text=f"Asked by {interaction.user.display_name}  •  AI-Powered")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="would-you-rather", description="AI-generated would you rather. Different every time, never repeats.")
    @app_commands.describe(theme="Optional theme (e.g. tech, food, superpowers, dark, funny)")
    async def would_you_rather(self, interaction: discord.Interaction, theme: str = ""):
        await interaction.response.defer()
        t = f" about {theme}" if theme else ""
        prompt = f"Generate ONE unique interesting 'Would You Rather'{t} question with exactly 2 options. Format: 'Option A OR Option B'. Just the options, no other text."
        try:
            result = await self.bot.nvidia.ask(prompt)
            parts = [p.strip().rstrip("?") for p in result.replace("Would you rather","").split(" OR ") if p.strip()]
            opt_a, opt_b = (parts[0], parts[1]) if len(parts) >= 2 else ("Have unlimited money", "Live forever")
        except Exception:
            opt_a, opt_b = "Have unlimited money", "Live forever"
        embed = comprehensive_embed(title="🤔  Would You Rather...", color=XERO.SECONDARY)
        embed.add_field(name="🅰️ Option A", value=f"**{opt_a}**", inline=False)
        embed.add_field(name="🅱️ Option B", value=f"**{opt_b}**", inline=False)
        if theme: embed.description = f"*Theme: {theme}*"
        embed.set_footer(text="React 🅰️ or 🅱️ to vote")
        msg = await interaction.followup.send(embed=embed)
        try: await msg.add_reaction("🅰️"); await msg.add_reaction("🅱️")
        except Exception: pass

    @app_commands.command(name="never-have-i-ever", description="AI-generated Never Have I Ever. Fresh every time.")
    @app_commands.describe(theme="Optional theme (gaming, travel, school, etc.)")
    async def never_have_i_ever(self, interaction: discord.Interaction, theme: str = ""):
        await interaction.response.defer()
        t = f" related to {theme}" if theme else ""
        prompt = f"Generate ONE creative 'Never Have I Ever' statement{t}. Start with '...'. Just the statement, no other text."
        try:
            result = await self.bot.nvidia.ask(prompt)
            stmt = result.strip()
            if not stmt.startswith("..."): stmt = "..." + stmt
        except Exception:
            stmt = "...accidentally sent a text to the wrong person."
        embed = comprehensive_embed(title="🙈  Never Have I Ever...", description=f"## {stmt}", color=XERO.PRIMARY)
        embed.set_footer(text="🤚 Done it  |  👏 Never done it")
        msg = await interaction.followup.send(embed=embed)
        try: await msg.add_reaction("🤚"); await msg.add_reaction("👏")
        except Exception: pass

    @app_commands.command(name="fortune", description="Your personal AI fortune cookie. Personalized to you.")
    async def fortune(self, interaction: discord.Interaction):
        await interaction.response.defer()
        prompt = f"Write a fortune cookie message for someone named {interaction.user.display_name}. Poetic, mystical, personal. 2-3 sentences max."
        try: text = await self.bot.nvidia.ask(prompt)
        except Exception: text = "Your path ahead is bright. Trust your instincts, for they know the way."
        embed = comprehensive_embed(title="🥠  Your Fortune", description=f"*{text}*", color=XERO.GOLD)
        embed.set_author(name=interaction.user.display_name, icon_url=interaction.user.display_avatar.url)
        embed.set_footer(text="XERO Fortune Cookie  •  The future is yours")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="roast", description="Get AI-roasted. Brutal but harmless.")
    @app_commands.describe(user="Who to roast (default: yourself)")
    async def roast(self, interaction: discord.Interaction, user: discord.Member = None):
        await interaction.response.defer()
        target = user or interaction.user
        prompt = f"Write a funny, clever, lighthearted roast of a Discord user named {target.display_name}. 2-3 sentences. Witty not mean. Reference being on Discord."
        try: text = await self.bot.nvidia.ask(prompt)
        except Exception: text = f"{target.display_name} is so online, their dreams have loading screens."
        embed = comprehensive_embed(title=f"🔥  {target.display_name} Got Roasted", description=text, color=XERO.ERROR)
        embed.set_thumbnail(url=target.display_avatar.url)
        embed.set_footer(text="All in good fun  •  XERO Roast Machine")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="compliment", description="Give someone a genuine AI-crafted compliment.")
    @app_commands.describe(user="Who to compliment")
    async def compliment(self, interaction: discord.Interaction, user: discord.Member):
        await interaction.response.defer()
        prompt = f"Write a genuine, heartfelt, specific compliment for someone named {user.display_name}. Not generic. 2 sentences max."
        try: text = await self.bot.nvidia.ask(prompt)
        except Exception: text = f"{user.display_name} has the kind of energy that makes every conversation better."
        embed = comprehensive_embed(title=f"💛  A Note for {user.display_name}", description=text, color=XERO.SUCCESS)
        embed.set_author(name=f"From {interaction.user.display_name}", icon_url=interaction.user.display_avatar.url)
        embed.set_thumbnail(url=user.display_avatar.url)
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="trivia", description="AI trivia — first correct answer wins. Scores tracked.")
    @app_commands.describe(category="Category (science, history, gaming, music, movies, etc.)")
    async def trivia(self, interaction: discord.Interaction, category: str = "general knowledge"):
        await interaction.response.defer()
        prompt = (
            f"Generate ONE trivia question about {category}. "
            f"Format EXACTLY:\nQ: [question]\nA: [answer]\nHINT: [one-word hint]\n"
            f"Answer must be short (1-4 words). Make it genuinely challenging."
        )
        try:
            result = await self.bot.nvidia.ask(prompt)
            lines = result.strip().split('\n')
            q = next((l.replace('Q:','').strip() for l in lines if l.startswith('Q:')), None)
            a = next((l.replace('A:','').strip() for l in lines if l.startswith('A:')), None)
            h = next((l.replace('HINT:','').strip() for l in lines if l.startswith('HINT:')), "think")
            if not q or not a: raise ValueError()
        except Exception:
            q, a, h = "What is the largest planet in our solar system?", "Jupiter", "space"

        expires = datetime.datetime.now() + datetime.timedelta(seconds=30)
        TRIVIA_ACTIVE[interaction.channel.id] = {"answer": a.lower().strip(), "expires": expires, "guild_id": interaction.guild.id, "question": q}
        embed = comprehensive_embed(title=f"🧠  Trivia — {category.title()}", color=XERO.PRIMARY)
        embed.add_field(name="❓ Question", value=f"**{q}**", inline=False)
        embed.add_field(name="💡 Hint",     value=f"*{h}*",   inline=True)
        embed.add_field(name="⏰ Time",     value="30 seconds", inline=True)
        embed.set_footer(text="Type your answer in chat!")
        await interaction.followup.send(embed=embed)
        await asyncio.sleep(30)
        if TRIVIA_ACTIVE.get(interaction.channel.id):
            TRIVIA_ACTIVE.pop(interaction.channel.id, None)
            reveal = comprehensive_embed(title="⏰  Time's Up!", description=f"Nobody got it!\n**Answer:** {a}", color=XERO.ERROR)
            try: await interaction.channel.send(embed=reveal)
            except Exception: pass

    @app_commands.command(name="trivia-scores", description="Trivia leaderboard for this server.")
    async def trivia_scores(self, interaction: discord.Interaction):
        gid = interaction.guild.id
        scores = TRIVIA_SCORES.get(gid, {})
        if not scores:
            return await interaction.response.send_message(embed=info_embed("No Scores", "No trivia scores yet. Use `/fun trivia` to start!"))
        sorted_s = sorted(scores.items(), key=lambda x: x[1].get('correct',0), reverse=True)[:10]
        medals = ["🥇","🥈","🥉"]+[f"`#{i}`" for i in range(4,11)]
        lines = []
        for i,(uid,d) in enumerate(sorted_s):
            m = interaction.guild.get_member(uid)
            name = m.display_name if m else f"User {uid}"
            total = d['correct'] + d.get('wrong',0)
            acc   = int(d['correct']/max(total,1)*100)
            lines.append(f"{medals[i]} **{name}** — {d['correct']} ✅ | {acc}% acc | 🔥{d.get('streak',0)}")
        embed = comprehensive_embed(title="🧠  Trivia Leaderboard", description="\n".join(lines), color=XERO.PRIMARY)
        embed.set_footer(text="XERO Trivia  •  /fun trivia to play")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="joke", description="AI-generated joke. Tell it what style you want.")
    @app_commands.describe(style="Style: dark, clean, pun, nerd, dad, roast, absurd")
    async def joke(self, interaction: discord.Interaction, style: str = "clean"):
        await interaction.response.defer()
        prompt = (
            f"Tell me ONE original {style} joke. "
            f"Format:\nSETUP: [setup]\nPUNCHLINE: [punchline]\nMake it genuinely funny."
        )
        try:
            result = await self.bot.nvidia.ask(prompt)
            lines  = result.strip().split('\n')
            setup  = next((l.replace('SETUP:','').strip() for l in lines if 'SETUP:' in l), None)
            punch  = next((l.replace('PUNCHLINE:','').strip() for l in lines if 'PUNCHLINE:' in l), None)
            if not setup or not punch: raise ValueError()
        except Exception:
            setup = "Why don't scientists trust atoms?"; punch = "Because they make up everything."
        embed = discord.Embed(color=XERO.GOLD)
        embed.add_field(name="😐", value=setup,          inline=False)
        embed.add_field(name="😂", value=f"||{punch}||", inline=False)
        embed.set_footer(text=f"{style.title()} joke  •  Click spoiler for punchline")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="ship", description="Calculate love compatibility between two users.")
    @app_commands.describe(user1="First person", user2="Second person")
    async def ship(self, interaction: discord.Interaction, user1: discord.Member, user2: discord.Member):
        score = (user1.id + user2.id) % 101
        if score > 90:   label, color = "💞 Soulmates!", 0xFF0000
        elif score > 75: label, color = "❤️ Great Match!", 0xFF6B6B
        elif score > 50: label, color = "💛 Pretty Compatible", XERO.GOLD
        elif score > 25: label, color = "🤝 Could Work", XERO.WARNING
        else:            label, color = "💔 Tough Road Ahead", XERO.PRIMARY
        bar = "💗" * (score // 10) + "🖤" * (10 - score // 10)
        name = user1.display_name[:len(user1.display_name)//2] + user2.display_name[len(user2.display_name)//2:]
        embed = comprehensive_embed(title="💘  Love Calculator", color=discord.Color(color))
        embed.add_field(name="💑 Ship Name", value=f"**{name}**",          inline=True)
        embed.add_field(name="💯 Score",     value=f"**{score}%** {label}", inline=True)
        embed.add_field(name="💗 Meter",     value=bar,                     inline=False)
        embed.set_footer(text=f"{user1.display_name} + {user2.display_name}")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="roll", description="Roll custom dice. NdS+M notation (e.g. 2d20+5).")
    @app_commands.describe(dice="Dice notation like 2d6, 1d20+3, 4d6")
    async def roll(self, interaction: discord.Interaction, dice: str = "1d6"):
        try:
            modifier = 0; d = dice.lower().replace(" ","")
            if "+" in d: d, mod = d.split("+",1); modifier = int(mod)
            elif "-" in d and "d" in d and d.index("-") > d.index("d"): d, mod = d.split("-",1); modifier = -int(mod)
            count, sides = map(int, d.split("d"))
            count = max(1, min(50, count)); sides = max(2, min(1000, sides))
            rolls = [random.randint(1, sides) for _ in range(count)]
            total = sum(rolls) + modifier
            mod_s = f" + {modifier}" if modifier > 0 else (f" - {abs(modifier)}" if modifier < 0 else "")
            crit  = " 🎯 **CRIT!**" if count==1 and rolls[0]==sides else (" 💀 **FAIL**" if count==1 and rolls[0]==1 else "")
            embed = comprehensive_embed(title=f"🎲  {dice}", color=XERO.PRIMARY)
            embed.add_field(name="🎲 Rolls", value=", ".join(map(str, rolls[:20])), inline=False)
            embed.add_field(name="📊 Total", value=f"**{total}**{mod_s}{crit}", inline=True)
            if len(rolls) > 1: embed.add_field(name="📈 High/Low", value=f"{max(rolls)} / {min(rolls)}", inline=True)
            await interaction.response.send_message(embed=embed)
        except Exception:
            await interaction.response.send_message(embed=error_embed("Invalid Dice","Use format like `2d6`, `1d20+5`."), ephemeral=True)

    @app_commands.command(name="choose", description="Can't decide? Let XERO pick. Comma-separated options.")
    @app_commands.describe(options="Options separated by commas")
    async def choose(self, interaction: discord.Interaction, options: str):
        choices = [o.strip() for o in options.split(",") if o.strip()]
        if len(choices) < 2: return await interaction.response.send_message(embed=error_embed("Too Few","Give at least 2 options."), ephemeral=True)
        chosen = random.choice(choices)
        embed = comprehensive_embed(title="🎯  Decision Made", color=XERO.SUCCESS)
        embed.add_field(name="🗳️ Options", value="\n".join(f"• {c}" for c in choices[:10]), inline=True)
        embed.add_field(name="✅ Chosen",  value=f"**{chosen}**", inline=True)
        embed.set_footer(text=f"Out of {len(choices)} options")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="meme", description="Fetch a fresh meme from Reddit.")
    @app_commands.describe(subreddit="Subreddit (memes, dankmemes, wholesomememes, etc.)")
    async def meme(self, interaction: discord.Interaction, subreddit: str = "memes"):
        await interaction.response.defer()
        safe_subs = {"memes","dankmemes","me_irl","wholesomememes","technicallythetruth","programmerhumor","unexpected","cursedcomments"}
        sub = subreddit.lower().strip("r/") if subreddit.lower().strip("r/") in safe_subs else "memes"
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get(f"https://www.reddit.com/r/{sub}/random.json?limit=1",
                                 headers={"User-Agent":"XERO-Bot/1.0"}, timeout=aiohttp.ClientTimeout(total=8)) as r:
                    if r.status != 200: raise Exception()
                    data = await r.json()
            post = data[0]["data"]["children"][0]["data"]
            url  = post.get("url","")
            if post.get("over_18") or not any(url.endswith(e) for e in [".jpg",".png",".gif",".jpeg"]): raise Exception()
            embed = comprehensive_embed(title=post["title"][:200], color=XERO.PRIMARY, url=f"https://reddit.com{post['permalink']}")
            embed.set_image(url=url)
            embed.set_footer(text=f"r/{sub}  •  👍 {post.get('ups',0):,}")
            await interaction.followup.send(embed=embed)
        except Exception:
            await interaction.followup.send(embed=error_embed("No Meme",f"Couldn't load from r/{sub}. Try r/memes."))

    @app_commands.command(name="cat", description="Random cat photo.")
    async def cat(self, interaction: discord.Interaction):
        await interaction.response.defer()
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get("https://api.thecatapi.com/v1/images/search", timeout=aiohttp.ClientTimeout(total=5)) as r:
                    data = await r.json()
            embed = comprehensive_embed(title="🐱  Meow!", color=0xFF9999)
            embed.set_image(url=data[0]["url"])
            embed.set_footer(text="XERO Fun  •  /fun dog for dogs")
            await interaction.followup.send(embed=embed)
        except Exception: await interaction.followup.send(embed=error_embed("Cat Error","Couldn't fetch a cat right now."))

    @app_commands.command(name="dog", description="Random dog photo.")
    async def dog(self, interaction: discord.Interaction):
        await interaction.response.defer()
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get("https://dog.ceo/api/breeds/image/random", timeout=aiohttp.ClientTimeout(total=5)) as r:
                    data = await r.json()
            embed = comprehensive_embed(title="🐶  Woof!", color=0xADD8E6)
            embed.set_image(url=data["message"])
            embed.set_footer(text="XERO Fun  •  /fun cat for cats")
            await interaction.followup.send(embed=embed)
        except Exception: await interaction.followup.send(embed=error_embed("Dog Error","Couldn't fetch a dog right now."))

    @app_commands.command(name="rps", description="Rock Paper Scissors vs XERO.")
    @app_commands.choices(choice=[
        app_commands.Choice(name="🪨 Rock",     value="rock"),
        app_commands.Choice(name="📄 Paper",    value="paper"),
        app_commands.Choice(name="✂️ Scissors", value="scissors"),
    ])
    async def rps(self, interaction: discord.Interaction, choice: str):
        bot_c  = random.choice(["rock","paper","scissors"])
        emojis = {"rock":"🪨","paper":"📄","scissors":"✂️"}
        wins   = {"rock":"scissors","paper":"rock","scissors":"paper"}
        if choice == bot_c:       result, color = "🤝  Tie!",       XERO.WARNING
        elif wins[choice]==bot_c: result, color = "🎉  You Win!",   XERO.SUCCESS
        else:                     result, color = "💀  XERO Wins!", XERO.ERROR
        embed = comprehensive_embed(title="✊  Rock Paper Scissors", color=discord.Color(color))
        embed.add_field(name=f"You: {emojis[choice]}",  value=choice.title(),  inline=True)
        embed.add_field(name=f"XERO: {emojis[bot_c]}", value=bot_c.title(), inline=True)
        embed.add_field(name="Result", value=result, inline=False)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="rate", description="AI rates anything you throw at it.")
    @app_commands.describe(thing="What to rate")
    async def rate(self, interaction: discord.Interaction, thing: str):
        await interaction.response.defer()
        prompt = f"Rate '{thing}' 1-10. Format:\nSCORE: X\nREASON: [one witty sentence]. Be creative and specific."
        try:
            result = await self.bot.nvidia.ask(prompt)
            lines  = result.strip().split('\n')
            s_line = next((l.replace('SCORE:','').strip() for l in lines if 'SCORE:' in l), "7")
            r_line = next((l.replace('REASON:','').strip() for l in lines if 'REASON:' in l), "It exists, and that's something.")
            score  = max(1, min(10, int(''.join(c for c in s_line if c.isdigit())[:2] or "7")))
        except Exception:
            score = random.randint(1, 10); r_line = "XERO's neural network had feelings about this."
        stars = "⭐" * score + "☆" * (10-score)
        color = XERO.SUCCESS if score >= 7 else XERO.WARNING if score >= 4 else XERO.ERROR
        embed = comprehensive_embed(title=f"📊  XERO Rates: {thing[:50]}", color=discord.Color(color))
        embed.add_field(name="Score",   value=f"**{score}/10**", inline=True)
        embed.add_field(name="Stars",   value=stars,              inline=True)
        embed.add_field(name="Verdict", value=r_line,             inline=False)
        embed.set_footer(text="XERO Rate Machine  •  All opinions are final")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="fact", description="AI fact about anything. Surprising and specific.")
    @app_commands.describe(topic="Topic (optional)")
    async def fact(self, interaction: discord.Interaction, topic: str = ""):
        await interaction.response.defer()
        t = f" about {topic}" if topic else ""
        prompt = f"Share one genuinely fascinating, true, lesser-known fact{t}. 2-3 sentences max. Make it surprising."
        try: text = await self.bot.nvidia.ask(prompt)
        except Exception: text = "Honey never spoils. 3,000-year-old honey found in Egyptian tombs was still edible."
        embed = comprehensive_embed(title="🤯  Random Fact", description=text, color=XERO.PRIMARY)
        embed.set_footer(text=f"{'Topic: ' + topic + '  •  ' if topic else ''}XERO Facts  •  Powered by Nemotron")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="debate", description="XERO argues both sides of any topic.")
    @app_commands.describe(topic="Topic to debate (e.g. 'pineapple on pizza')")
    async def debate(self, interaction: discord.Interaction, topic: str):
        await interaction.response.defer()
        prompt = f"Briefly debate both sides of: '{topic}'\nFOR: [2 sharp sentences supporting it]\nAGAINST: [2 sharp sentences opposing it]\nBe funny and persuasive on both sides."
        try:
            result  = await self.bot.nvidia.ask(prompt)
            lines   = result.strip().split('\n')
            for_txt = next((l.replace('FOR:','').strip() for l in lines if l.startswith('FOR:')), "There are valid arguments in favor.")
            against = next((l.replace('AGAINST:','').strip() for l in lines if l.startswith('AGAINST:')), "But the other side makes sense too.")
        except Exception:
            for_txt = "There are valid arguments in favor."; against = "But the other side makes sense too."
        embed = comprehensive_embed(title=f"⚖️  Debate: {topic[:60]}", color=XERO.SECONDARY)
        embed.add_field(name="✅ For",     value=for_txt, inline=False)
        embed.add_field(name="❌ Against", value=against, inline=False)
        embed.set_footer(text="XERO takes no sides  •  React to vote")
        msg = await interaction.followup.send(embed=embed)
        try: await msg.add_reaction("✅"); await msg.add_reaction("❌")
        except Exception: pass

    # Trivia answer listener
    @commands.Cog.listener()
    async def on_message(self, message: discord.Message):
        if message.author.bot or not message.guild: return
        active = TRIVIA_ACTIVE.get(message.channel.id)
        if not active: return
        if datetime.datetime.now() > active["expires"]:
            TRIVIA_ACTIVE.pop(message.channel.id, None); return
        if message.content.lower().strip() == active["answer"]:
            TRIVIA_ACTIVE.pop(message.channel.id, None)
            gid = message.guild.id; uid = message.author.id
            if gid not in TRIVIA_SCORES: TRIVIA_SCORES[gid] = {}
            if uid not in TRIVIA_SCORES[gid]: TRIVIA_SCORES[gid][uid] = {"correct":0,"wrong":0,"streak":0}
            TRIVIA_SCORES[gid][uid]["correct"] += 1
            TRIVIA_SCORES[gid][uid]["streak"]  += 1
            streak = TRIVIA_SCORES[gid][uid]["streak"]
            embed = comprehensive_embed(title="🎉  Correct!", description=f"**{message.author.mention}** got it!\n**Answer:** {active['answer'].title()}", color=XERO.SUCCESS)
            if streak >= 3: embed.add_field(name="🔥 Hot Streak", value=f"**{streak}** in a row!", inline=True)
            try: await message.reply(embed=embed)
            except Exception: pass


async def setup(bot):
    await bot.add_cog(Fun(bot))
