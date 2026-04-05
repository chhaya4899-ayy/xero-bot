"""
XERO Bot — Aegis Neural AutoMod Protocol v2
8-rule real-time enforcement engine. Every check isolated in its own try/except.
Bulletproof: one failing check never stops the others.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, aiosqlite, asyncio, datetime, re
from collections import defaultdict
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed, XERO

logger = logging.getLogger("XERO.AutoMod")

# ── Default word filter (always active when anti_profanity=1) ─────────────────
DEFAULT_BANNED_WORDS = [
    "fuck", "niga", "nigah", "niger", "nigger", "bitch", "asshole", "ass hole",
    "shit", "cunt", "pussy", "dick", "faggot", "retard", "slut", "whore",
    "bastard", "motherfucker", "nigga", "niggah", "nigg", "fag", "fagg",
    "kike", "spic", "chink", "coon", "wetback", "gook", "raghead",
    "towelhead", "paki", "kyke", "dyke", "tranny", "shemale",
]

# Always-allowed domains even when anti_links is on
ALWAYS_ALLOWED = {"discord.com", "discord.gg", "tenor.com", "giphy.com",
                  "discordapp.com", "cdn.discordapp.com"}

URL_RE     = re.compile(r'https?://\S+|www\.\S+', re.IGNORECASE)
INVITE_RE  = re.compile(r'(discord\.gg/|discord\.com/invite/)\S+', re.IGNORECASE)
EMOJI_RE   = re.compile(
    r'[\U0001F000-\U0001FFFF]|[\U00002702-\U000027B0]|'
    r'[\U0001F300-\U0001F5FF]|[\U0001F600-\U0001F64F]|'
    r'[\U0001F680-\U0001F6FF]|<a?:\w+:\d+>',
    re.UNICODE
)


class AegisAutoMod(commands.GroupCog, name="automod"):
    def __init__(self, bot):
        self.bot = bot
        # {guild_id: {user_id: [timestamps]}}
        self.spam_tracker     = defaultdict(lambda: defaultdict(list))
        self.new_acct_tracker = defaultdict(lambda: defaultdict(list))

    # ──────────────────────────────────────────────────────────────────────
    # Config helpers
    # ──────────────────────────────────────────────────────────────────────

    async def get_config(self, guild_id: int) -> dict:
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM automod_config WHERE guild_id=?", (guild_id,)
                ) as c:
                    row = await c.fetchone()
            if row:
                return dict(row)
        except Exception as e:
            logger.warning(f"get_config: {e}")
        return {
            "guild_id": guild_id, "enabled": 0, "anti_spam": 1,
            "anti_links": 0, "anti_caps": 0, "anti_profanity": 1,
            "anti_emoji_spam": 0, "anti_invite": 0, "anti_new_account": 0,
            "max_mentions": 5, "spam_threshold": 5,
            "log_channel_id": None, "action": "delete",
        }

    async def _upsert_config(self, guild_id: int, **kwargs):
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS automod_config (
                    guild_id INTEGER PRIMARY KEY, enabled INTEGER DEFAULT 0,
                    anti_spam INTEGER DEFAULT 1, anti_links INTEGER DEFAULT 0,
                    anti_caps INTEGER DEFAULT 0, anti_profanity INTEGER DEFAULT 1,
                    anti_emoji_spam INTEGER DEFAULT 0, anti_invite INTEGER DEFAULT 0,
                    anti_new_account INTEGER DEFAULT 0, max_mentions INTEGER DEFAULT 5,
                    spam_threshold INTEGER DEFAULT 5, log_channel_id INTEGER,
                    action TEXT DEFAULT 'delete',
                    new_account_mute_minutes INTEGER DEFAULT 10
                )
            """)
            existing = await self.get_config(guild_id)
            if existing.get("guild_id"):
                sets = ", ".join(f"{k}=?" for k in kwargs)
                vals = list(kwargs.values()) + [guild_id]
                await db.execute(f"UPDATE automod_config SET {sets} WHERE guild_id=?", vals)
            else:
                cols = "guild_id, " + ", ".join(kwargs.keys())
                phs  = ", ".join("?" for _ in range(len(kwargs) + 1))
                await db.execute(
                    f"INSERT INTO automod_config ({cols}) VALUES ({phs})",
                    [guild_id] + list(kwargs.values())
                )
            await db.commit()

    # ──────────────────────────────────────────────────────────────────────
    # Strike DB helpers
    # ──────────────────────────────────────────────────────────────────────

    async def get_strikes(self, guild_id: int, user_id: int) -> int:
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT strikes FROM automod_strikes WHERE guild_id=? AND user_id=?",
                    (guild_id, user_id)
                ) as c:
                    row = await c.fetchone()
                return row[0] if row else 0
        except Exception:
            return 0

    async def increment_strike(self, guild_id: int, user_id: int) -> int:
        """Add a strike, return new total."""
        try:
            async with self.bot.db._db_context() as db:
                await db.execute("""
                    INSERT INTO automod_strikes (user_id, guild_id, strikes, last_strike)
                    VALUES (?, ?, 1, datetime('now'))
                    ON CONFLICT(user_id, guild_id) DO UPDATE SET
                        strikes = strikes + 1,
                        last_strike = datetime('now')
                """, (user_id, guild_id))
                await db.commit()
                async with db.execute(
                    "SELECT strikes FROM automod_strikes WHERE user_id=? AND guild_id=?",
                    (user_id, guild_id)
                ) as c:
                    row = await c.fetchone()
                return row[0] if row else 1
        except Exception as e:
            logger.warning(f"increment_strike: {e}")
            return 1

    async def get_word_filters(self, guild_id: int) -> list:
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT value FROM automod_filters WHERE guild_id=? AND filter_type='word'",
                    (guild_id,)
                ) as c:
                    return [r[0].lower() for r in await c.fetchall()]
        except Exception:
            return []

    async def get_allowed_domains(self, guild_id: int) -> set:
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT domain FROM allowed_domains WHERE guild_id=?", (guild_id,)
                ) as c:
                    rows = await c.fetchall()
            return ALWAYS_ALLOWED | {r[0].lower() for r in rows}
        except Exception:
            return ALWAYS_ALLOWED

    # ──────────────────────────────────────────────────────────────────────
    # Log + DM helpers
    # ──────────────────────────────────────────────────────────────────────

    async def _log(self, guild, user, action_taken: str, rule: str, content: str = None):
        try:
            config = await self.get_config(guild.id)
            ch_id  = config.get("log_channel_id")
            if not ch_id:
                return
            ch = guild.get_channel(ch_id)
            if not ch:
                return
            embed = discord.Embed(
                title="🛡️  AutoMod Action",
                color=discord.Color(0xED4245),
                timestamp=discord.utils.utcnow()
            )
            embed.add_field(name="User",         value=f"{user.mention} (`{user.id}`)", inline=True)
            embed.add_field(name="Action",       value=action_taken, inline=True)
            embed.add_field(name="Rule Broken",  value=rule, inline=False)
            if content:
                preview = content[:400]
                embed.add_field(name="Message Content", value=f"```{preview}```", inline=False)
            embed.set_thumbnail(url=user.display_avatar.url)
            embed.set_footer(text="XERO AutoMod  •  Real-Time Enforcement")
            await ch.send(embed=embed)
        except Exception as e:
            logger.debug(f"_log failed: {e}")

    async def _dm_user(self, user: discord.Member, rule: str, guild_name: str, strikes: int = 1):
        """Detailed educational DM — explains what happened, what the rule is, and the consequences."""
        try:
            # Strike-level messaging
            if strikes >= 3:
                title  = "⛔  Enforcement Action Taken"
                color  = discord.Color(0xED4245)
                action_note = (
                    "**This was your 3rd or higher violation.** "
                    "An additional penalty (timeout, kick, or ban) may have been applied to your account."
                )
            elif strikes == 2:
                title  = "⚠️  Second Warning — Next May Escalate"
                color  = discord.Color(0xFEE75C)
                action_note = (
                    "**This is your 2nd violation.** "
                    "One more violation will trigger an escalated action (timeout or higher)."
                )
            else:
                title  = "🛡️  Message Removed by AutoMod"
                color  = discord.Color(0xFFB800)
                action_note = "This is your first recorded violation. No additional action was taken."

            embed = discord.Embed(
                title=title,
                color=color,
                timestamp=discord.utils.utcnow()
            )
            embed.add_field(
                name="📍 Server",
                value=guild_name,
                inline=True
            )
            embed.add_field(
                name="📋 Rule Violated",
                value=rule,
                inline=True
            )
            embed.add_field(
                name="🔢 Strike Count",
                value=f"**{strikes}**",
                inline=True
            )
            embed.add_field(
                name="ℹ️ What This Means",
                value=action_note,
                inline=False
            )
            embed.add_field(
                name="📌 What To Do",
                value=(
                    "• Review the server rules\n"
                    "• If you believe this was a mistake, contact a moderator\n"
                    "• Continued violations will result in timeouts or removal"
                ),
                inline=False
            )
            embed.set_footer(text="XERO AutoMod  ·  Automated Enforcement  ·  Not a human message")
            await user.send(embed=embed)
        except discord.Forbidden:
            pass  # DMs disabled — skip silently
        except Exception as e:
            logger.debug(f"_dm_user failed: {e}")

    # ──────────────────────────────────────────────────────────────────────
    # Escalation engine
    # ──────────────────────────────────────────────────────────────────────

    async def _escalate(self, message: discord.Message, rule: str, config: dict) -> str:
        """
        Delete msg, increment strike, apply action based on strike count.
        Returns action string for logging.
        strike 1: delete + channel warn
        strike 2: delete + warn (note: next escalates)
        strike 3+: delete + configured action (timeout/kick/ban)
        """
        user  = message.author
        guild = message.guild

        try:
            await message.delete()
        except Exception:
            pass

        strikes = await self.increment_strike(guild.id, user.id)
        base    = config.get("action", "delete")
        action_taken = "Message deleted"

        if strikes >= 3:
            if base == "timeout":
                try:
                    until = discord.utils.utcnow() + datetime.timedelta(minutes=5)
                    await user.timeout(until, reason=f"XERO AutoMod ({strikes} strikes): {rule}")
                    action_taken = "5-minute timeout"
                except Exception as e:
                    logger.warning(f"timeout failed: {e}")
            elif base == "kick":
                try:
                    await user.kick(reason=f"XERO AutoMod ({strikes} strikes): {rule}")
                    action_taken = "Kicked"
                except Exception as e:
                    logger.warning(f"kick failed: {e}")
            elif base == "ban":
                try:
                    await user.ban(
                        reason=f"XERO AutoMod ({strikes} strikes): {rule}",
                        delete_message_days=1
                    )
                    action_taken = "Banned"
                except Exception as e:
                    logger.warning(f"ban failed: {e}")
            else:
                action_taken = f"Message deleted (strike {strikes})"
        elif strikes == 2:
            action_taken = "Message deleted (strike 2 — next violation escalates)"

        # Channel warning
        try:
            note = ""
            if strikes == 2:
                note = " — **next violation will escalate.**"
            elif strikes >= 3:
                note = " — **action has been taken against your account.**"
            await message.channel.send(
                f"🛡️ {user.mention} — AutoMod: **{rule}**{note}",
                delete_after=8
            )
        except Exception:
            pass

        await self._dm_user(user, rule, guild.name, strikes)
        return action_taken

    # ══════════════════════════════════════════════════════════════════════
    # PRIMARY ENTRY POINT — called from main.py on_message
    # ══════════════════════════════════════════════════════════════════════

    async def process_message(self, message: discord.Message) -> bool:
        """
        Run all 8 automod checks in order. Each check is wrapped in its own
        try/except so a crash in one never prevents the others from running.
        Returns True if the message was actioned (deleted / user penalised).
        """
        if message.author.bot or not message.guild:
            return False
        # Exempt users who can manage messages (mods/admins)
        try:
            if message.author.guild_permissions.manage_messages:
                return False
        except Exception:
            return False

        config = await self.get_config(message.guild.id)
        if not config.get("enabled"):
            return False

        # Check exempt channels
        try:
            async with self.bot.db._db_context() as db:
                try:
                    async with db.execute(
                        "SELECT 1 FROM automod_exempt_channels WHERE guild_id=? AND channel_id=?",
                        (message.guild.id, message.channel.id)
                    ) as cur:
                        if await cur.fetchone():
                            return False
                except Exception:
                    pass
                # Check exempt roles
                try:
                    user_role_ids = [r.id for r in message.author.roles]
                    if user_role_ids:
                        placeholders = ",".join("?" * len(user_role_ids))
                        async with db.execute(
                            f"SELECT 1 FROM automod_exempt_roles WHERE guild_id=? AND role_id IN ({placeholders})",
                            [message.guild.id] + user_role_ids
                        ) as cur:
                            if await cur.fetchone():
                                return False
                except Exception:
                    pass
        except Exception:
            pass

        gid = message.guild.id
        uid = message.author.id

        # ── Check 1: Anti-Spam (burst) ─────────────────────────────────────
        try:
            if config.get("anti_spam", 1):
                now  = datetime.datetime.now()
                hist = self.spam_tracker[gid][uid]
                hist.append(now)
                # Prune to last 5 seconds
                self.spam_tracker[gid][uid] = [
                    t for t in hist if (now - t).total_seconds() < 5
                ]
                if len(self.spam_tracker[gid][uid]) >= config.get("spam_threshold", 5):
                    self.spam_tracker[gid][uid] = []  # reset burst window

                    # Bulk-delete the burst
                    try:
                        async def _is_burst(m):
                            return (m.author.id == uid and
                                    (now - m.created_at.replace(tzinfo=None)).total_seconds() < 8)
                        await message.channel.purge(limit=20, check=lambda m: (
                            m.author.id == uid and
                            (now - m.created_at.replace(tzinfo=None)).total_seconds() < 8
                        ))
                    except Exception:
                        try:
                            await message.delete()
                        except Exception:
                            pass

                    strikes = await self.increment_strike(gid, uid)
                    base    = config.get("action", "delete")
                    action  = "Burst purge"

                    if strikes >= 3:
                        if base == "timeout":
                            try:
                                until = discord.utils.utcnow() + datetime.timedelta(minutes=5)
                                await message.author.timeout(until, reason="XERO AutoMod: Spam burst")
                                action = "Burst purge + 5m timeout"
                            except Exception:
                                pass
                        elif base == "kick":
                            try:
                                await message.author.kick(reason="XERO AutoMod: Spam burst")
                                action = "Kicked for spam burst"
                            except Exception:
                                pass

                    try:
                        await message.channel.send(
                            f"🛡️ {message.author.mention} — **Anti-Spam:** slow down! "
                            f"(strike {strikes})",
                            delete_after=8
                        )
                    except Exception:
                        pass

                    await self._dm_user(
                        message.author,
                        "Anti-Spam: sending messages too quickly",
                        message.guild.name,
                        strikes
                    )
                    await self._log(message.guild, message.author, action,
                                    "Anti-Spam: message burst detected", message.content[:200])
                    return True
        except Exception as e:
            logger.error(f"Check1 anti-spam: {e}")

        # ── Check 2: Anti-Caps ─────────────────────────────────────────────
        try:
            if config.get("anti_caps", 0):
                text    = message.content
                letters = [c for c in text if c.isalpha()]
                if len(text) >= 8 and letters:
                    caps_ratio = sum(1 for c in letters if c.isupper()) / len(letters)
                    if caps_ratio >= 0.75:
                        action = await self._escalate(
                            message,
                            "Anti-Caps: message is 75%+ uppercase",
                            config
                        )
                        await self._log(message.guild, message.author, action,
                                        "Anti-Caps", message.content[:200])
                        return True
        except Exception as e:
            logger.error(f"Check2 anti-caps: {e}")

        # ── Check 3: Mention spam ──────────────────────────────────────────
        try:
            max_mentions = config.get("max_mentions", 5)
            # Count unique user mentions + role mentions
            mention_count = len(set(m.id for m in message.mentions)) + len(message.role_mentions)
            if mention_count >= max_mentions:
                try:
                    await message.delete()
                except Exception:
                    pass
                # Mention spam always timeouts — no config required
                try:
                    until = discord.utils.utcnow() + datetime.timedelta(minutes=5)
                    await message.author.timeout(
                        until, reason=f"XERO AutoMod: Mention spam ({mention_count} mentions)"
                    )
                except Exception:
                    pass
                try:
                    await message.channel.send(
                        f"🛡️ {message.author.mention} — **Mention Spam:** {mention_count} mentions "
                        f"is above the limit of {max_mentions}. (5m timeout)",
                        delete_after=8
                    )
                except Exception:
                    pass
                await self._dm_user(
                    message.author,
                    f"Mention Spam: {mention_count} mentions in a single message (limit: {max_mentions})",
                    message.guild.name, 1
                )
                await self._log(message.guild, message.author,
                                "5-minute timeout",
                                f"Mention Spam: {mention_count} mentions",
                                message.content[:200])
                return True
        except Exception as e:
            logger.error(f"Check3 mention-spam: {e}")

        # ── Check 4: Word filter ───────────────────────────────────────────
        try:
            if config.get("anti_profanity", 1):
                content_lower = message.content.lower()
                custom_words  = await self.get_word_filters(gid)
                all_words     = set(DEFAULT_BANNED_WORDS) | set(custom_words)
                hit = False
                for word in all_words:
                    if word in content_lower:
                        hit = True
                        break
                if hit:
                    # Note: we tell user they broke the rule, NOT what word triggered it
                    action = await self._escalate(
                        message,
                        "Word Filter: prohibited language",
                        config
                    )
                    await self._log(message.guild, message.author, action,
                                    "Word Filter: prohibited language",
                                    "[content redacted for privacy]")
                    return True
        except Exception as e:
            logger.error(f"Check4 word-filter: {e}")

        # ── Check 5: Emoji spam ────────────────────────────────────────────
        try:
            if config.get("anti_emoji_spam", 0):
                emoji_count = len(EMOJI_RE.findall(message.content))
                if emoji_count >= 8:
                    action = await self._escalate(
                        message,
                        f"Emoji Spam: {emoji_count} emojis in one message (limit: 8)",
                        config
                    )
                    await self._log(message.guild, message.author, action,
                                    f"Emoji Spam: {emoji_count} emojis", message.content[:200])
                    return True
        except Exception as e:
            logger.error(f"Check5 emoji-spam: {e}")

        # ── Check 6: Anti-links (external URLs) ────────────────────────────
        try:
            if config.get("anti_links", 0):
                urls = URL_RE.findall(message.content)
                if urls:
                    allowed = await self.get_allowed_domains(gid)
                    for url in urls:
                        try:
                            domain = url.split("//")[-1].split("/")[0].lower().lstrip("www.")
                            base   = ".".join(domain.split(".")[-2:]) if "." in domain else domain
                        except Exception:
                            domain, base = "", ""
                        if domain not in allowed and base not in allowed:
                            action = await self._escalate(
                                message,
                                "Anti-Links: external URL not in allowed list",
                                config
                            )
                            await self._log(message.guild, message.author, action,
                                            f"Anti-Links: blocked domain ({base})",
                                            message.content[:200])
                            return True
        except Exception as e:
            logger.error(f"Check6 anti-links: {e}")

        # ── Check 7: Invite links ──────────────────────────────────────────
        try:
            if config.get("anti_invite", 0):
                if INVITE_RE.search(message.content):
                    action = await self._escalate(
                        message,
                        "Anti-Invite: Discord server invites are not allowed here",
                        config
                    )
                    await self._log(message.guild, message.author, action,
                                    "Anti-Invite: Discord invite link", message.content[:200])
                    return True
        except Exception as e:
            logger.error(f"Check7 anti-invite: {e}")

        # ── Check 8: New account spam ──────────────────────────────────────
        try:
            if config.get("anti_new_account", 0):
                age_days = (discord.utils.utcnow() - message.author.created_at).days
                if age_days < 7:
                    now  = datetime.datetime.now()
                    hist = self.new_acct_tracker[gid][uid]
                    hist.append(now)
                    self.new_acct_tracker[gid][uid] = [
                        t for t in hist if (now - t).total_seconds() < 30
                    ]
                    if len(self.new_acct_tracker[gid][uid]) >= 3:
                        self.new_acct_tracker[gid][uid] = []
                        mute_mins = config.get("new_account_mute_minutes", 10)
                        try:
                            await message.delete()
                        except Exception:
                            pass
                        try:
                            until = discord.utils.utcnow() + datetime.timedelta(minutes=mute_mins)
                            await message.author.timeout(
                                until,
                                reason=f"XERO AutoMod: New account ({age_days}d) spam burst"
                            )
                        except Exception:
                            pass
                        try:
                            await message.channel.send(
                                f"🛡️ {message.author.mention} — new accounts have a message "
                                f"rate limit. ({mute_mins}m timeout)",
                                delete_after=8
                            )
                        except Exception:
                            pass
                        await self._dm_user(
                            message.author,
                            f"New Account Restriction: accounts under 7 days old are rate-limited "
                            f"({mute_mins}-minute timeout applied)",
                            message.guild.name, 1
                        )
                        await self._log(
                            message.guild, message.author,
                            f"{mute_mins}m timeout",
                            f"New Account Spam: account is {age_days}d old, burst in 30s",
                            message.content[:200]
                        )
                        return True
        except Exception as e:
            logger.error(f"Check8 new-acct-spam: {e}")

        return False

    # ══════════════════════════════════════════════════════════════════════
    # SLASH COMMANDS
    # ══════════════════════════════════════════════════════════════════════

    @app_commands.command(name="setup",
                          description="Deploy XERO AutoMod with default safe settings.")
    @app_commands.describe(log_channel="Channel to log all automod actions")
    @app_commands.checks.has_permissions(administrator=True)
    async def setup(self, interaction: discord.Interaction,
                    log_channel: discord.TextChannel = None):
        await self._upsert_config(
            interaction.guild.id,
            enabled=1, anti_spam=1, anti_profanity=1, anti_invite=1,
            anti_links=0, anti_caps=0, anti_emoji_spam=0, anti_new_account=1,
            max_mentions=5, spam_threshold=5, action="delete",
            log_channel_id=log_channel.id if log_channel else None
        )

        # Try to deploy native Discord AutoMod rules too
        if interaction.guild.me.guild_permissions.manage_guild:
            try:
                await interaction.guild.create_automod_rule(
                    name="XERO Aegis: Profanity Filter",
                    event_type=discord.AutoModRuleEventType.message_send,
                    trigger_type=discord.AutoModRuleTriggerType.keyword,
                    trigger_metadata=discord.AutoModTriggerMetadata(
                        keyword_filter=DEFAULT_BANNED_WORDS[:100]  # Discord limit
                    ),
                    actions=[discord.AutoModRuleAction(
                        type=discord.AutoModRuleActionType.block_message
                    )],
                    enabled=True,
                    reason="XERO Aegis AutoMod Deployment"
                )
            except Exception as e:
                logger.warning(f"Native AutoMod deploy: {e}")

        embed = discord.Embed(
            title="✅  XERO AutoMod — Deployed",
            description=(
                "**8-rule real-time enforcement engine is now active.**\n\n"
                "Use `/automod toggle` to turn individual rules on/off.\n"
                "Use `/automod action` to set the penalty tier.\n"
                "Use `/automod word-filter` to manage custom banned words.\n"
                "Use `/automod status` to see the full configuration."
            ),
            color=discord.Color(0x57F287),
            timestamp=discord.utils.utcnow()
        )
        embed.add_field(name="Active by Default", value=(
            "✅ Anti-Spam  •  ✅ Word Filter  •  ✅ Anti-Invite\n"
            "✅ Mention Spam  •  ✅ New Account Spam"
        ), inline=False)
        embed.add_field(name="Off by Default (enable with /automod toggle)", value=(
            "❌ Anti-Caps  •  ❌ Emoji Spam  •  ❌ Anti-Links"
        ), inline=False)
        if log_channel:
            embed.add_field(name="Log Channel", value=log_channel.mention, inline=True)
        embed.set_footer(text="XERO AutoMod  •  Bulletproof Real-Time Enforcement")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="toggle",
                          description="Enable or disable a specific AutoMod rule.")
    @app_commands.describe(rule="Which rule to toggle", enabled="True to enable, False to disable")
    @app_commands.choices(rule=[
        app_commands.Choice(name="Anti-Spam (burst)",      value="anti_spam"),
        app_commands.Choice(name="Anti-Caps (75%+ caps)",  value="anti_caps"),
        app_commands.Choice(name="Word Filter",            value="anti_profanity"),
        app_commands.Choice(name="Emoji Spam (8+ emojis)", value="anti_emoji_spam"),
        app_commands.Choice(name="Anti-Links (ext URLs)",  value="anti_links"),
        app_commands.Choice(name="Anti-Invite",            value="anti_invite"),
        app_commands.Choice(name="New Account Spam",       value="anti_new_account"),
    ])
    @app_commands.checks.has_permissions(manage_guild=True)
    async def toggle(self, interaction: discord.Interaction, rule: str, enabled: bool):
        await self._upsert_config(interaction.guild.id, **{rule: 1 if enabled else 0})
        status = "✅ Enabled" if enabled else "❌ Disabled"
        friendly = rule.replace("_", " ").title()
        await interaction.response.send_message(
            embed=success_embed("AutoMod Rule Updated",
                                f"**{friendly}** → {status}"),
            ephemeral=True
        )

    @app_commands.command(name="action",
                          description="Set the penalty for 3+ strikes.")
    @app_commands.choices(action=[
        app_commands.Choice(name="Delete only",      value="delete"),
        app_commands.Choice(name="Timeout (5 min)",  value="timeout"),
        app_commands.Choice(name="Kick",             value="kick"),
        app_commands.Choice(name="Ban",              value="ban"),
    ])
    @app_commands.checks.has_permissions(manage_guild=True)
    async def set_action(self, interaction: discord.Interaction, action: str):
        await self._upsert_config(interaction.guild.id, action=action)
        await interaction.response.send_message(
            embed=success_embed("Penalty Updated",
                                f"3rd-strike action → **{action}**"),
            ephemeral=True
        )

    @app_commands.command(name="word-filter",
                          description="Add or remove words from the custom filter.")
    @app_commands.describe(add="Word to add", remove="Word to remove")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def word_filter(self, interaction: discord.Interaction,
                          add: str = None, remove: str = None):
        async with self.bot.db._db_context() as db:
            if add:
                w = add.lower().strip()
                await db.execute(
                    "INSERT OR IGNORE INTO automod_filters (guild_id, filter_type, value) "
                    "VALUES (?,?,?)",
                    (interaction.guild.id, "word", w)
                )
            if remove:
                w = remove.lower().strip()
                await db.execute(
                    "DELETE FROM automod_filters WHERE guild_id=? AND filter_type='word' AND value=?",
                    (interaction.guild.id, w)
                )
            await db.commit()

        words = await self.get_word_filters(interaction.guild.id)
        custom_list = ", ".join(f"`{w}`" for w in words[:30]) if words else "*None added yet*"
        embed = success_embed(
            "Word Filter Updated",
            f"**Custom words ({len(words)}):**\n{custom_list}\n\n"
            f"*Default banned words are always active regardless of this list.*"
        )
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="status",
                          description="View the full AutoMod configuration.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def status(self, interaction: discord.Interaction):
        config = await self.get_config(interaction.guild.id)
        def t(v): return "✅" if v else "❌"

        embed = comprehensive_embed(
            title=f"🛡️  AutoMod Status — {interaction.guild.name}",
            color=XERO.PRIMARY
        )
        system_status = "✅ **ACTIVE**" if config.get("enabled") else "❌ **INACTIVE** — run `/automod setup`"
        embed.add_field(name="System Status", value=system_status, inline=False)
        embed.add_field(name="Rules", value=(
            f"{t(config.get('anti_spam',1))} Anti-Spam  "
            f"(burst threshold: **{config.get('spam_threshold',5)}** msgs/5s)\n"
            f"{t(config.get('anti_caps',0))} Anti-Caps  (≥75% uppercase, ≥8 chars)\n"
            f"{t(config.get('anti_profanity',1))} Word Filter  (defaults + custom)\n"
            f"{t(config.get('anti_emoji_spam',0))} Emoji Spam  (≥8 emojis)\n"
            f"{t(config.get('anti_links',0))} Anti-Links  (ext URLs)\n"
            f"{t(config.get('anti_invite',0))} Anti-Invite  (discord.gg links)\n"
            f"{t(config.get('anti_new_account',0))} New Account Spam  (<7 day accounts)\n"
            f"✅ Mention Spam  (≥**{config.get('max_mentions',5)}** mentions auto-timeout)"
        ), inline=False)
        embed.add_field(
            name="Penalty (3rd strike)",
            value=f"`{config.get('action','delete')}`",
            inline=True
        )
        ch_id = config.get("log_channel_id")
        embed.add_field(
            name="Log Channel",
            value=f"<#{ch_id}>" if ch_id else "*Not set*",
            inline=True
        )
        embed.set_footer(text="XERO AutoMod  •  /automod toggle to enable/disable rules")
        await interaction.response.send_message(embed=embed)


    @app_commands.command(name="exempt-channel", description="Exempt a channel from AutoMod enforcement.")
    @app_commands.describe(channel="Channel to exempt (or un-exempt)", exempt="True to exempt, False to remove exemption")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def exempt_channel(self, interaction: discord.Interaction, channel: discord.TextChannel, exempt: bool = True):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "CREATE TABLE IF NOT EXISTS automod_exempt_channels (guild_id INTEGER, channel_id INTEGER, PRIMARY KEY(guild_id, channel_id))"
            )
            if exempt:
                await db.execute(
                    "INSERT OR IGNORE INTO automod_exempt_channels (guild_id, channel_id) VALUES (?,?)",
                    (interaction.guild.id, channel.id)
                )
            else:
                await db.execute(
                    "DELETE FROM automod_exempt_channels WHERE guild_id=? AND channel_id=?",
                    (interaction.guild.id, channel.id)
                )
            await db.commit()
        if exempt:
            await interaction.response.send_message(
                embed=success_embed("Channel Exempted", f"{channel.mention} is now **exempt** from AutoMod — messages there will not be enforced."),
                ephemeral=True
            )
        else:
            await interaction.response.send_message(
                embed=success_embed("Exemption Removed", f"{channel.mention} will now be **enforced** by AutoMod."),
                ephemeral=True
            )

    @app_commands.command(name="exempt-role", description="Exempt a role from AutoMod enforcement.")
    @app_commands.describe(role="Role to exempt (or un-exempt)", exempt="True to exempt, False to remove exemption")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def exempt_role(self, interaction: discord.Interaction, role: discord.Role, exempt: bool = True):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "CREATE TABLE IF NOT EXISTS automod_exempt_roles (guild_id INTEGER, role_id INTEGER, PRIMARY KEY(guild_id, role_id))"
            )
            if exempt:
                await db.execute(
                    "INSERT OR IGNORE INTO automod_exempt_roles (guild_id, role_id) VALUES (?,?)",
                    (interaction.guild.id, role.id)
                )
            else:
                await db.execute(
                    "DELETE FROM automod_exempt_roles WHERE guild_id=? AND role_id=?",
                    (interaction.guild.id, role.id)
                )
            await db.commit()
        if exempt:
            await interaction.response.send_message(
                embed=success_embed("Role Exempted", f"{role.mention} members are now **exempt** from AutoMod enforcement."),
                ephemeral=True
            )
        else:
            await interaction.response.send_message(
                embed=success_embed("Exemption Removed", f"{role.mention} members will now be **enforced** by AutoMod."),
                ephemeral=True
            )

    @app_commands.command(name="clear-strikes", description="Clear all AutoMod strikes for a user.")
    @app_commands.describe(user="User to clear strikes for")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def clear_strikes(self, interaction: discord.Interaction, user: discord.Member):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "UPDATE automod_strikes SET strikes=0 WHERE guild_id=? AND user_id=?",
                (interaction.guild.id, user.id)
            )
            await db.commit()
        await interaction.response.send_message(
            embed=success_embed("Strikes Cleared", f"AutoMod strikes for {user.mention} have been reset to 0."),
            ephemeral=True
        )

    @app_commands.command(name="strikes", description="View AutoMod strike count for a user.")
    @app_commands.describe(user="User to check")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def view_strikes(self, interaction: discord.Interaction, user: discord.Member):
        strikes = await self.get_strikes(interaction.guild.id, user.id)
        embed = discord.Embed(
            title=f"🛡️ AutoMod Strikes — {user.display_name}",
            color=discord.Color(0xED4245) if strikes >= 3 else discord.Color(0xFFB800) if strikes >= 1 else discord.Color(0x57F287),
            timestamp=discord.utils.utcnow()
        )
        embed.set_thumbnail(url=user.display_avatar.url)
        embed.add_field(name="Strikes", value=f"**{strikes}** / 3", inline=True)
        embed.add_field(name="Status", value="🔴 At threshold" if strikes >= 3 else ("🟡 Warning" if strikes >= 1 else "🟢 Clean"), inline=True)
        embed.set_footer(text="XERO AutoMod  ·  3 strikes = escalation")
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @commands.Cog.listener()
    async def on_automod_action_execution(self, execution):
        """Bridge native Discord AutoMod → XERO log channel."""
        if execution.action.type == discord.AutoModRuleActionType.block_message:
            await self._log(
                execution.guild, execution.member,
                "Native Discord AutoMod Block",
                f"Native AutoMod rule triggered (rule ID: {execution.rule_id})"
            )


async def setup(bot):
    await bot.add_cog(AegisAutoMod(bot))
