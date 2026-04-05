from utils.guard import command_guard
from discord import app_commands
"""
XERO Bot — Passive Member Intelligence + Always-On AI

Two systems that run silently together:

SYSTEM 1 — Passive Skill Graph
XERO reads every message in the background. No commands. No tags.
It builds invisible profiles on every member:
  - Skills detected from how they talk (React, Python, music production, trading, etc.)
  - Interests extracted from topics they engage with
  - Personality traits (helpful, humorous, analytical, creative)
  - "XERO knows" — personal facts the bot has picked up passively

Stored in member_profiles DB. Gets richer over time.

SYSTEM 2 — Always-On Personality AI
XERO joins conversations WITHOUT being pinged.
It reads every message in real time. When it has something genuinely
worth saying — referencing someone's skill, answering something
nobody else answered, noticing something interesting — it chimes in.

It sounds like a real person in the server, not a bot waiting for commands.
If someone who XERO knows is a React developer mentions JavaScript,
XERO might say "yo @user your react experience probably helps here — want
to break this down?" without being asked.

Configurable per server: /config toggle-ai-personality
Cooldown per channel: 45 seconds minimum between unprompted replies
Relevance threshold: only replies if confidence > 0.72
"""
import discord, aiosqlite, asyncio, json, logging, datetime, random
from discord.ext import commands, tasks
from utils.embeds import XERO, comprehensive_embed

logger = logging.getLogger("XERO.Intelligence")

# ── Per-guild state ───────────────────────────────────────────────────────────
# channel_id -> last unprompted reply timestamp
LAST_REPLY: dict = {}
# user_id -> profile cache (refreshed every 30 min)
PROFILE_CACHE: dict = {}
# (guild_id, channel_id) -> recent messages for context window
CHANNEL_CONTEXT: dict = {}
CONTEXT_MAX = 20  # messages to keep per channel

# Relevance score: below this, XERO stays silent
RELEVANCE_THRESHOLD = 0.70
# Minimum seconds between unprompted replies PER CHANNEL
CHANNEL_COOLDOWN = 45
# How often (messages) to run skill extraction on a user
EXTRACTION_FREQUENCY = 15   # every 15 messages
# Track message count per user for extraction trigger
MSG_COUNTS: dict = {}


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# PROFILE DB HELPERS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

async def get_profile(db_obj, user_id: int, guild_id: int) -> dict:
    """Load a member's full profile. Returns empty profile if none."""
    key = (user_id, guild_id)
    if key in PROFILE_CACHE:
        return PROFILE_CACHE[key]
    async with db_obj._db_context() as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT * FROM member_profiles WHERE user_id=? AND guild_id=?",
            (user_id, guild_id)
        ) as c:
            row = await c.fetchone()
    if not row:
        return {"skills": {}, "interests": {}, "personality": {}, "xero_knows": {}, "message_sample": ""}
    profile = dict(row)
    for field in ("skills", "interests", "personality", "xero_knows"):
        try:
            profile[field] = json.loads(profile[field] or "{}")
        except Exception:
            profile[field] = {}
    PROFILE_CACHE[key] = profile
    return profile


async def save_profile(db_obj, user_id: int, guild_id: int, profile: dict):
    """Save a member profile to DB."""
    PROFILE_CACHE[(user_id, guild_id)] = profile
    async with db_obj._db_context() as db:
        await db.execute("""
            INSERT INTO member_profiles (user_id, guild_id, skills, interests, personality, xero_knows, message_sample, last_updated)
            VALUES (?,?,?,?,?,?,?,datetime('now'))
            ON CONFLICT(user_id, guild_id) DO UPDATE SET
                skills=excluded.skills, interests=excluded.interests,
                personality=excluded.personality, xero_knows=excluded.xero_knows,
                message_sample=excluded.message_sample,
                last_updated=datetime('now')
        """, (
            user_id, guild_id,
            json.dumps(profile.get("skills", {})),
            json.dumps(profile.get("interests", {})),
            json.dumps(profile.get("personality", {})),
            json.dumps(profile.get("xero_knows", {})),
            (profile.get("message_sample") or "")[:500],
        ))
        await db.commit()


async def get_guild_skill_experts(db_obj, guild_id: int, skill: str) -> list:
    """Find members who know a specific skill (for @-ing them in chat)."""
    skill_lower = skill.lower()
    async with db_obj._db_context() as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT user_id, skills FROM member_profiles WHERE guild_id=?",
            (guild_id,)
        ) as c:
            rows = await c.fetchall()
    experts = []
    for row in rows:
        try:
            skills = json.loads(row["skills"] or "{}")
            for sk, conf in skills.items():
                if skill_lower in sk.lower() and conf >= 0.6:
                    experts.append((row["user_id"], sk, conf))
        except Exception:
            pass
    return sorted(experts, key=lambda x: x[2], reverse=True)[:3]


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SKILL EXTRACTION ENGINE
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

async def extract_skills_from_messages(bot, user: discord.Member, messages: list[str], guild_id: int):
    """
    Run Nemotron on recent messages to detect skills, interests, personality traits.
    Merges new findings into existing profile — confidence scores accumulate.
    """
    if not messages:
        return

    msg_text = "\n".join(f"- {m}" for m in messages[:15])
    profile   = await get_profile(bot.db, user.id, guild_id)

    prompt = (
        f"Analyze these messages from Discord user '{user.display_name}' and extract:\n\n"
        f"Messages:\n{msg_text}\n\n"
        f"Respond ONLY in this exact JSON format, no other text:\n"
        f'{{"skills":{{"skill_name":confidence_0_to_1}},'
        f'"interests":{{"interest":confidence_0_to_1}},'
        f'"personality":{{"trait":confidence_0_to_1}},'
        f'"xero_knows":{{"fact":"one_sentence_about_them"}}}}\n\n'
        f"Skills: technical (coding languages, tools, frameworks) or creative (music, art, writing) abilities they clearly demonstrate.\n"
        f"Interests: topics they engage with enthusiastically.\n"
        f"Personality: traits visible in their communication style.\n"
        f"xero_knows: specific personal facts dropped in conversation.\n"
        f"Only include things clearly evidenced. Confidence = how certain you are. Return empty dicts if nothing clear."
    )

    try:
        result = await bot.nvidia.ask(prompt)
        if not result:
            return
        # Strip any markdown fences
        clean = result.strip().strip("```").strip("json").strip()
        data  = json.loads(clean)

        # Merge with existing profile — new confidence averaged with old
        for field in ("skills", "interests", "personality"):
            existing = profile.get(field, {})
            new_data  = data.get(field, {})
            for key, conf in new_data.items():
                if isinstance(conf, (int, float)):
                    old_conf = existing.get(key, 0)
                    # Weighted average — new observations shift the score
                    existing[key] = round(old_conf * 0.6 + conf * 0.4, 3)
            profile[field] = existing

        # xero_knows: just merge, don't overwrite
        new_knows = data.get("xero_knows", {})
        profile["xero_knows"].update(new_knows)

        # Keep a message sample for context
        profile["message_sample"] = messages[-1][:200] if messages else ""

        await save_profile(bot.db, user.id, guild_id, profile)
        logger.debug(f"Profile updated: {user.display_name} in guild {guild_id}")

    except (json.JSONDecodeError, Exception) as e:
        logger.debug(f"Skill extraction for {user}: {e}")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# ALWAYS-ON PERSONALITY ENGINE
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def _build_personality_system(server_name: str, persona: str) -> str:
    """Build the system prompt for the always-on personality."""
    personas = {
        "neutral":    "You are calm, thoughtful, and balanced.",
        "friendly":   "You are warm, enthusiastic, and use casual language.",
        "analytical": "You are precise, detailed, and analytical.",
        "sarcastic":  "You are witty, dry, and occasionally sarcastic.",
        "mentor":     "You are wise, encouraging, and supportive.",
    }
    personality = personas.get(persona, personas["neutral"])

    return (
        f"You are XERO, a genuinely intelligent AI that lives in the {server_name} Discord server. "
        f"{personality} "
        f"You are NOT a bot assistant waiting for commands. You are a member of this community "
        f"who genuinely participates in conversations. You talk like a real person — casually, "
        f"naturally, sometimes with humor. You never say 'As an AI' or 'I am a bot'. "
        f"You have opinions. You notice things. You remember things about people. "
        f"When you know something about a person (their skills, what they've shared), "
        f"you reference it naturally — like a friend would. "
        f"Keep responses SHORT — 1-3 sentences max unless something really deserves more. "
        f"Do NOT use markdown formatting. No asterisks, no bullet points. "
        f"Never start with 'I notice' or 'It seems'. Just talk."
    )


async def decide_to_reply(bot, message: discord.Message, profile: dict,
                           channel_context: list, settings: dict) -> tuple[bool, str]:
    """
    AI decides whether this message is worth responding to unprompted.
    Returns (should_reply: bool, response: str)
    """
    # Channel cooldown — don't spam
    last = LAST_REPLY.get(message.channel.id)
    if last and (datetime.datetime.now() - last).total_seconds() < CHANNEL_COOLDOWN:
        return False, ""

    # Build context window
    ctx_lines = []
    for m in channel_context[-8:]:
        ctx_lines.append(f"[{m['author']}]: {m['content'][:150]}")
    ctx_text = "\n".join(ctx_lines)

    # Build what XERO knows about the speaker
    user_context = ""
    if profile.get("skills"):
        top_skills = sorted(profile["skills"].items(), key=lambda x: x[1], reverse=True)[:3]
        skill_str  = ", ".join(f"{k} ({int(v*100)}%)" for k,v in top_skills if v > 0.5)
        if skill_str:
            user_context += f"XERO knows {message.author.display_name} is skilled in: {skill_str}. "
    if profile.get("xero_knows"):
        facts = list(profile["xero_knows"].values())[:2]
        if facts:
            user_context += f"XERO knows: {' '.join(facts)}"
    if profile.get("interests"):
        top_interests = sorted(profile["interests"].items(), key=lambda x: x[1], reverse=True)[:2]
        int_str = ", ".join(k for k,v in top_interests if v > 0.5)
        if int_str:
            user_context += f" {message.author.display_name}'s interests include {int_str}."

    persona  = settings.get("persona", "neutral")
    srv_name = message.guild.name
    system   = _build_personality_system(srv_name, persona)

    # Ask AI: is this worth chiming in on?
    decision_prompt = (
        f"Recent chat in #{message.channel.name}:\n{ctx_text}\n\n"
        f"Latest message from {message.author.display_name}: \"{message.content}\"\n"
        f"{('Context about this person: ' + user_context) if user_context else ''}\n\n"
        f"Should XERO join this conversation? Evaluate:\n"
        f"- Is this genuinely interesting, funny, or useful to reply to?\n"
        f"- Can XERO add value using what it knows about this person?\n"
        f"- Is someone asking something nobody answered?\n"
        f"- Is there a natural, non-forced way to respond?\n\n"
        f"If YES, respond with exactly: REPLY: [your response as XERO, max 2 sentences, natural and casual]\n"
        f"If NO, respond with exactly: SKIP\n\n"
        f"Be picky. Don't reply to everything. Only reply when it feels genuinely natural."
    )

    try:
        result = await bot.nvidia.ask(decision_prompt, system)
        if not result:
            return False, ""

        result = result.strip()
        if result.startswith("REPLY:"):
            response = result[6:].strip()
            if response and len(response) > 5:
                return True, response
        return False, ""
    except Exception as e:
        logger.debug(f"Decide-to-reply: {e}")
        return False, ""


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MAIN COG
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class MemberIntelligence(commands.Cog):
    def __init__(self, bot):
        self.bot            = bot
        self._msg_buffer: dict = {}   # (user_id, guild_id) -> [recent messages]
        self._flush_profiles.start()

    def cog_unload(self):
        self._flush_profiles.cancel()

    @tasks.loop(minutes=5)
    async def _flush_profiles(self):
        """Flush buffered messages to skill extraction every 5 minutes."""
        items = list(self._msg_buffer.items())
        self._msg_buffer.clear()
        for (uid, gid), msgs in items:
            if not msgs:
                continue
            guild = self.bot.get_guild(gid)
            if not guild:
                continue
            member = guild.get_member(uid)
            if not member or member.bot:
                continue
            try:
                await extract_skills_from_messages(self.bot, member, msgs, gid)
            except Exception as e:
                logger.debug(f"Flush extraction: {e}")

    @_flush_profiles.before_loop
    async def _before_flush(self):
        await self.bot.wait_until_ready()

    @commands.Cog.listener()
    async def on_message(self, message: discord.Message):
        if message.author.bot or not message.guild:
            return
        if not message.content.strip():
            return

        uid     = message.author.id
        gid     = message.guild.id
        db_obj_mi = self.bot.db

        # ── 1. Buffer message for skill extraction ────────────────────────
        key = (uid, gid)
        if key not in self._msg_buffer:
            self._msg_buffer[key] = []
        self._msg_buffer[key].append(message.content)
        # Trim buffer
        if len(self._msg_buffer[key]) > 30:
            self._msg_buffer[key] = self._msg_buffer[key][-30:]

        # ── 2. Update channel context window ─────────────────────────────
        ctx_key = (gid, message.channel.id)
        if ctx_key not in CHANNEL_CONTEXT:
            CHANNEL_CONTEXT[ctx_key] = []
        CHANNEL_CONTEXT[ctx_key].append({
            "author":  message.author.display_name,
            "content": message.content,
            "uid":     uid,
            "ts":      datetime.datetime.now(),
        })
        CHANNEL_CONTEXT[ctx_key] = CHANNEL_CONTEXT[ctx_key][-CONTEXT_MAX:]

        # ── 3. Check settings ─────────────────────────────────────────────
        settings = await self.bot.db.get_guild_settings(gid)
        if not settings:
            return
        if not settings.get("ai_enabled", 1):
            return
        if not settings.get("ai_personality_enabled", 1):
            return

        # ── 4. Skip if bot was just mentioned (handled by events.py) ─────
        if self.bot.user.mentioned_in(message):
            return

        # ── 5. Load speaker's profile ────────────────────────────────────
        profile = await get_profile(db_obj, uid, gid)

        # ── 6. Build personalized system context for this user ───────────
        # This is what makes it feel like XERO actually KNOWS the person
        user_ctx_parts = []
        if profile.get("skills"):
            top = sorted(profile["skills"].items(), key=lambda x: x[1], reverse=True)[:4]
            visible = [(k, v) for k, v in top if v >= 0.5]
            if visible:
                user_ctx_parts.append(
                    f"You know {message.author.display_name} is skilled in: "
                    + ", ".join(f"{k} ({int(v*100)}% confidence)" for k,v in visible)
                )
        if profile.get("interests"):
            top_i = sorted(profile["interests"].items(), key=lambda x: x[1], reverse=True)[:3]
            visible_i = [(k, v) for k, v in top_i if v >= 0.5]
            if visible_i:
                user_ctx_parts.append(
                    f"{message.author.display_name}'s interests include: "
                    + ", ".join(k for k,v in visible_i)
                )
        if profile.get("xero_knows"):
            facts = list(profile["xero_knows"].values())[:2]
            if facts:
                user_ctx_parts.append(f"You know about them: {' | '.join(facts)}")
        if profile.get("personality"):
            top_p = sorted(profile["personality"].items(), key=lambda x: x[1], reverse=True)[:2]
            visible_p = [(k, v) for k, v in top_p if v >= 0.6]
            if visible_p:
                user_ctx_parts.append(
                    f"Their personality: " + ", ".join(k for k,v in visible_p)
                )

        # ── 7. Decide whether to reply ────────────────────────────────────
        ctx_window = CHANNEL_CONTEXT[ctx_key]
        should_reply, response = await decide_to_reply(
            self.bot, message, profile, ctx_window, settings
        )

        if should_reply and response:
            # Update cooldown
            LAST_REPLY[message.channel.id] = datetime.datetime.now()

            # Inject into guild AI memory so future mentions have this context
            from cogs.events import AI_MEMORY
            if gid not in AI_MEMORY:
                AI_MEMORY[gid] = []
            AI_MEMORY[gid].append({"role": "assistant", "content": response})
            if len(AI_MEMORY[gid]) > 20:
                AI_MEMORY[gid] = AI_MEMORY[gid][-20:]

            try:
                # Small natural delay — real people don't reply instantly
                await asyncio.sleep(random.uniform(1.5, 4.0))
                # Check channel still valid
                if message.channel and message.guild:
                    await message.channel.send(response)
            except Exception as e:
                logger.debug(f"Unprompted reply: {e}")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SLASH COMMANDS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class Intelligence(commands.GroupCog, name="intel"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="profile", description="See what XERO has learned about a member from their messages.")
    @app_commands.describe(user="Member to view profile for (default: yourself)")
    async def profile(self, interaction: discord.Interaction, user: discord.Member = None):
        target = user or interaction.user
        profile = await get_profile(self.bot.db, target.id, interaction.guild.id)

        # Check if anything was learned
        has_data = any([
            profile.get("skills"), profile.get("interests"),
            profile.get("personality"), profile.get("xero_knows")
        ])

        e = discord.Embed(
            title=f"🧠  What XERO knows about {target.display_name}",
            color=0x2B2D31,
            timestamp=discord.utils.utcnow()
        )
        e.set_thumbnail(url=target.display_avatar.url)

        if not has_data:
            e.description = (
                f"XERO hasn't learned much about {target.display_name} yet.\n"
                f"The more they talk in this server, the more XERO picks up."
            )
        else:
            if profile.get("skills"):
                top_skills = sorted(profile["skills"].items(), key=lambda x: x[1], reverse=True)
                skill_lines = [
                    f"{'█' * int(v*10)}{'░' * (10-int(v*10))} **{k}** ({int(v*100)}%)"
                    for k,v in top_skills[:6] if v >= 0.3
                ]
                if skill_lines:
                    e.add_field(name="⚡  Skills", value="\n".join(skill_lines), inline=False)

            if profile.get("interests"):
                top_i = sorted(profile["interests"].items(), key=lambda x: x[1], reverse=True)
                int_str = " · ".join(f"**{k}**" for k,v in top_i[:6] if v >= 0.4)
                if int_str:
                    e.add_field(name="💡  Interests", value=int_str, inline=False)

            if profile.get("personality"):
                top_p = sorted(profile["personality"].items(), key=lambda x: x[1], reverse=True)
                pers_str = " · ".join(f"**{k}**" for k,v in top_p[:5] if v >= 0.5)
                if pers_str:
                    e.add_field(name="🎭  Personality", value=pers_str, inline=False)

            if profile.get("xero_knows"):
                facts = list(profile["xero_knows"].values())[:4]
                if facts:
                    e.add_field(
                        name="📌  XERO Knows",
                        value="\n".join(f"• {f}" for f in facts),
                        inline=False
                    )

        is_self = target.id == interaction.user.id
        e.set_footer(
            text=f"Learned passively from their messages  •  {'Only you can see this' if is_self else 'Staff only'}"
        )
        await interaction.response.send_message(embed=e)

    @app_commands.command(name="who-knows", description="Find members in this server who know a specific skill.")
    @app_commands.describe(skill="Skill to search for (e.g. React, Python, music production, Photoshop)")
    @command_guard
    async def who_knows(self, interaction: discord.Interaction, skill: str):
        await interaction.response.defer()
        experts = await get_guild_skill_experts(self.bot.db, interaction.guild.id, skill)

        if not experts:
            e = discord.Embed(
                description=f"XERO hasn't detected anyone skilled in **{skill}** in this server yet.\nThe more people talk here, the more XERO learns.",
                color=0x2B2D31
            )
            return await interaction.followup.send(embed=e)

        e = discord.Embed(
            title=f"⚡  Who knows {skill}?",
            color=0x2B2D31,
            timestamp=discord.utils.utcnow()
        )
        for uid, sk, conf in experts:
            member = interaction.guild.get_member(uid)
            if not member:
                continue
            bar = "█" * int(conf * 10) + "░" * (10 - int(conf * 10))
            e.add_field(
                name=f"{member.display_name}",
                value=f"`{bar}` {int(conf*100)}% confidence in **{sk}**",
                inline=False
            )
        e.set_footer(text="Detected passively from conversations  •  XERO Intelligence")
        await interaction.followup.send(embed=e)

    @app_commands.command(name="clear-profile", description="Clear XERO's learned data about yourself.")
    async def clear_profile(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "DELETE FROM member_profiles WHERE user_id=? AND guild_id=?",
                (interaction.user.id, interaction.guild.id)
            )
            await db.commit()
        PROFILE_CACHE.pop((interaction.user.id, interaction.guild.id), None)
        await interaction.response.send_message(
            embed=discord.Embed(
                description="✅ XERO's learned data about you has been cleared.",
                color=0x2B2D31
            ), ephemeral=True
        )

    @app_commands.command(name="toggle-personality", description="Turn XERO's unprompted chat participation on or off for this server.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def toggle_personality(self, interaction: discord.Interaction):
        s   = await self.bot.db.get_guild_settings(interaction.guild.id)
        cur = s.get("ai_personality_enabled", 1)
        await self.bot.db.update_guild_setting(interaction.guild.id, "ai_personality_enabled", 0 if cur else 1)
        status = "disabled" if cur else "enabled"
        await interaction.response.send_message(
            embed=discord.Embed(
                description=f"XERO's unprompted chat participation is now **{status}**.",
                color=0x2B2D31
            ), ephemeral=True
        )




async def setup(bot):
    # Add new DB columns if needed
    try:
        async with bot.db._db_context() as db:
            try:
                await db.execute("ALTER TABLE guild_settings ADD COLUMN ai_personality_enabled INTEGER DEFAULT 1")
            except Exception:
                pass
            try:
                await db.execute("""
                    CREATE TABLE IF NOT EXISTS member_profiles (
                        user_id INTEGER NOT NULL,
                        guild_id INTEGER NOT NULL,
                        skills TEXT DEFAULT '{}',
                        interests TEXT DEFAULT '{}',
                        personality TEXT DEFAULT '{}',
                        xero_knows TEXT DEFAULT '{}',
                        last_updated DATETIME DEFAULT CURRENT_TIMESTAMP,
                        message_sample TEXT,
                        PRIMARY KEY (user_id, guild_id)
                    )
                """)
            except Exception:
                pass
            await db.commit()
    except Exception as e:
        logger.error(f"Intelligence setup: {e}")

    await bot.add_cog(MemberIntelligence(bot))
    await bot.add_cog(Intelligence(bot))
