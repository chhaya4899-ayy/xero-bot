"""
XERO Bot — Auto-Responder, Sticky Messages, Highlights, Tags
These are the Carl-bot and Dyno premium features everyone wants.
All free, all better (AI-powered responses).
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, asyncio, aiosqlite, re
from utils.embeds import success_embed, error_embed, info_embed, XERO, comprehensive_embed

logger = logging.getLogger("XERO.AutoResponder")

# Sticky message cache: channel_id -> message_id (the last sticky message)
STICKY_CACHE: dict = {}
# Highlight cache: guild_id -> {user_id -> [keywords]}
HIGHLIGHT_CACHE: dict = {}


class AutoResponder(commands.GroupCog, name="autoresponder"):
    def __init__(self, bot):
        self.bot = bot

    async def _ensure_tables(self):
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS autoresponders (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    trigger TEXT NOT NULL,
                    response TEXT NOT NULL,
                    match_type TEXT DEFAULT 'contains',
                    use_ai INTEGER DEFAULT 0,
                    case_sensitive INTEGER DEFAULT 0,
                    uses INTEGER DEFAULT 0,
                    created_by INTEGER,
                    UNIQUE(guild_id, trigger)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS sticky_messages (
                    channel_id INTEGER PRIMARY KEY,
                    guild_id INTEGER NOT NULL,
                    content TEXT NOT NULL,
                    embed_title TEXT,
                    embed_color TEXT DEFAULT '00D4FF',
                    last_message_id INTEGER,
                    enabled INTEGER DEFAULT 1
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS highlights (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    keyword TEXT NOT NULL,
                    UNIQUE(user_id, guild_id, keyword)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS tags (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    content TEXT NOT NULL,
                    embed_title TEXT,
                    uses INTEGER DEFAULT 0,
                    created_by INTEGER,
                    UNIQUE(guild_id, name)
                )
            """)
            await db.commit()

    # ── on_message handler (called by events.py or directly) ──────────────
    async def process_message(self, message: discord.Message):
        if message.author.bot or not message.guild:
            return
        await self._ensure_tables()

        # ── Auto-responders ────────────────────────────────────────────────
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM autoresponders WHERE guild_id=?",
                (message.guild.id,)
            ) as c:
                triggers = [dict(r) for r in await c.fetchall()]

        content = message.content
        for t in triggers:
            trigger  = t["trigger"]
            match_t  = t["match_type"]
            case_s   = t["case_sensitive"]
            haystack = content if case_s else content.lower()
            needle   = trigger if case_s else trigger.lower()

            matched = False
            if   match_t == "contains" and needle in haystack:    matched = True
            elif match_t == "startswith" and haystack.startswith(needle): matched = True
            elif match_t == "endswith"   and haystack.endswith(needle):   matched = True
            elif match_t == "exact"      and haystack.strip() == needle:  matched = True
            elif match_t == "regex":
                try:
                    if re.search(trigger, content, 0 if case_s else re.IGNORECASE):
                        matched = True
                except Exception:
                    pass

            if matched:
                try:
                    response = t["response"]
                    # Replace placeholders
                    response = response \
                        .replace("{user}", message.author.mention) \
                        .replace("{name}", message.author.display_name) \
                        .replace("{server}", message.guild.name) \
                        .replace("{channel}", message.channel.mention)

                    # AI-powered response
                    if t["use_ai"]:
                        ai_prompt = (
                            f"A user said: '{content}'\n"
                            f"Your response template: '{response}'\n"
                            f"Expand this into a helpful, natural Discord response. Keep it concise."
                        )
                        ai_response = await self.bot.nvidia.ask(ai_prompt)
                        response = ai_response or response

                    await message.channel.send(response)
                    async with self.bot.db._db_context() as db:
                        await db.execute("UPDATE autoresponders SET uses=uses+1 WHERE id=?", (t["id"],))
                        await db.commit()
                except Exception as e:
                    logger.error(f"Autoresponder error: {e}")
                break  # Only one response per message

        # ── Sticky messages ────────────────────────────────────────────────
        await self._check_sticky(message)

        # ── Highlights ────────────────────────────────────────────────────
        await self._check_highlights(message)

    async def _check_sticky(self, message: discord.Message):
        cid = message.channel.id
        async with self.bot.db._db_context() as db:
            async with db.execute(
                "SELECT * FROM sticky_messages WHERE channel_id=? AND enabled=1",
                (cid,)
            ) as c:
                sticky = await c.fetchone()
        if not sticky: return

        content, embed_title, color, last_id = sticky[2], sticky[3], sticky[4], sticky[5]

        # Delete old sticky
        if last_id:
            try:
                old_msg = await message.channel.fetch_message(last_id)
                await old_msg.delete()
            except Exception:
                pass

        # Resend sticky
        try:
            if embed_title:
                color_int = int(color.lstrip("#"), 16) if color else 0x00D4FF
                embed = comprehensive_embed(title=embed_title, description=content, color=discord.Color(color_int))
                embed.set_footer(text="📌 Sticky Message  •  XERO Bot")
                new_msg = await message.channel.send(embed=embed)
            else:
                new_msg = await message.channel.send(f"📌 **Sticky:** {content}")

            async with self.bot.db._db_context() as db:
                await db.execute(
                    "UPDATE sticky_messages SET last_message_id=? WHERE channel_id=?",
                    (new_msg.id, cid)
                )
                await db.commit()
        except Exception as e:
            logger.debug(f"Sticky resend: {e}")

    async def _check_highlights(self, message: discord.Message):
        gid = message.guild.id
        content_lower = message.content.lower()
        if not content_lower: return

        # Load highlights for this guild
        async with self.bot.db._db_context() as db:
            async with db.execute(
                "SELECT user_id, keyword FROM highlights WHERE guild_id=?",
                (gid,)
            ) as c:
                rows = await c.fetchall()

        user_keywords: dict = {}
        for uid, kw in rows:
            if uid not in user_keywords: user_keywords[uid] = []
            user_keywords[uid].append(kw.lower())

        for uid, keywords in user_keywords.items():
            if uid == message.author.id: continue  # Don't ping yourself
            matched_kw = [kw for kw in keywords if kw in content_lower]
            if not matched_kw: continue

            member = message.guild.get_member(uid)
            if not member: continue
            # Don't DM if the user is online and can see the channel
            perms = message.channel.permissions_for(member)
            if not perms.view_channel: continue

            try:
                embed = discord.Embed(
                    title="🔔  Keyword Highlight",
                    description=f"A keyword you're watching was mentioned in **{message.guild.name}**!",
                    color=XERO.PRIMARY
                )
                embed.add_field(name="🔑 Keywords",  value=", ".join(f"`{kw}`" for kw in matched_kw), inline=True)
                embed.add_field(name="👤 Author",    value=message.author.mention,                    inline=True)
                embed.add_field(name="📢 Channel",   value=message.channel.mention,                   inline=True)
                embed.add_field(name="💬 Message",   value=f"```{message.content[:500]}```",          inline=False)
                embed.add_field(name="🔗 Jump",      value=f"[View Message]({message.jump_url})",     inline=True)
                embed.set_footer(text="XERO Highlights  •  /highlight add <keyword> to track more")
                await member.send(embed=embed)
            except Exception:
                pass

    # ── /autoresponder add ────────────────────────────────────────────────
    @app_commands.command(name="add", description="Add an auto-response triggered when a keyword appears in chat.")
    @app_commands.describe(
        trigger="Word or phrase that triggers the response",
        response="What XERO replies with (use {user} {name} {server} {channel})",
        match_type="How to match the trigger",
        use_ai="Let AI expand the response for variety",
        case_sensitive="Case sensitive matching"
    )
    @app_commands.choices(match_type=[
        app_commands.Choice(name="Contains (anywhere in message)", value="contains"),
        app_commands.Choice(name="Exact match only",               value="exact"),
        app_commands.Choice(name="Starts with",                    value="startswith"),
        app_commands.Choice(name="Ends with",                      value="endswith"),
        app_commands.Choice(name="Regex pattern",                  value="regex"),
    ])
    @app_commands.checks.has_permissions(manage_messages=True)
    async def add(self, interaction: discord.Interaction, trigger: str, response: str,
                  match_type: str = "contains", use_ai: bool = False, case_sensitive: bool = False):
        await self._ensure_tables()
        async with self.bot.db._db_context() as db:
            try:
                await db.execute(
                    "INSERT INTO autoresponders (guild_id,trigger,response,match_type,use_ai,case_sensitive,created_by) VALUES (?,?,?,?,?,?,?)",
                    (interaction.guild.id, trigger, response, match_type, 1 if use_ai else 0, 1 if case_sensitive else 0, interaction.user.id)
                )
                await db.commit()
            except aiosqlite.IntegrityError:
                return await interaction.response.send_message(
                    embed=error_embed("Already Exists", f"An auto-responder for `{trigger}` already exists. Use `/autoresponder edit` to update it."),
                    ephemeral=True
                )

        embed = success_embed("Auto-Responder Added",
            f"**Trigger:** `{trigger}`\n"
            f"**Match:** {match_type}\n"
            f"**Response:** {response[:100]}\n"
            f"**AI-powered:** {'Yes' if use_ai else 'No'}\n"
            f"**Case sensitive:** {'Yes' if case_sensitive else 'No'}"
        )
        await interaction.response.send_message(embed=embed)

    # ── /autoresponder list ───────────────────────────────────────────────
    @app_commands.command(name="list", description="View all auto-responders with usage stats.")
    async def list(self, interaction: discord.Interaction):
        await self._ensure_tables()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM autoresponders WHERE guild_id=? ORDER BY uses DESC",
                (interaction.guild.id,)
            ) as c:
                rows = [dict(r) for r in await c.fetchall()]

        if not rows:
            return await interaction.response.send_message(embed=info_embed("No Auto-Responders", "Add one with `/autoresponder add`."))

        embed = comprehensive_embed(title=f"🤖  Auto-Responders ({len(rows)})", color=XERO.AI if hasattr(XERO,'AI') else XERO.PRIMARY)
        for r in rows[:10]:
            ai_tag = " [AI]" if r["use_ai"] else ""
            embed.add_field(
                name=f"`{r['trigger']}`  •  {r['uses']} uses{ai_tag}",
                value=f"{r['response'][:60]}{'...' if len(r['response'])>60 else ''}\n*{r['match_type']}*",
                inline=False
            )
        embed.set_footer(text="XERO Auto-Responder  •  /autoresponder add to add more")
        await interaction.response.send_message(embed=embed)

    # ── /autoresponder remove ─────────────────────────────────────────────
    @app_commands.command(name="remove", description="Remove an auto-responder by its trigger word.")
    @app_commands.describe(trigger="Trigger to remove")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def remove(self, interaction: discord.Interaction, trigger: str):
        await self._ensure_tables()
        async with self.bot.db._db_context() as db:
            await db.execute(
                "DELETE FROM autoresponders WHERE guild_id=? AND LOWER(trigger)=LOWER(?)",
                (interaction.guild.id, trigger)
            )
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Removed", f"Auto-responder for `{trigger}` deleted."))

    # ── /autoresponder test ───────────────────────────────────────────────
    @app_commands.command(name="test", description="Test a trigger to see if it would fire an auto-response.")
    @app_commands.describe(message="The message to test against all auto-responders")
    async def test(self, interaction: discord.Interaction, message: str):
        await self._ensure_tables()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM autoresponders WHERE guild_id=?", (interaction.guild.id,)) as c:
                triggers = [dict(r) for r in await c.fetchall()]

        matches = []
        for t in triggers:
            h = message if t["case_sensitive"] else message.lower()
            n = t["trigger"] if t["case_sensitive"] else t["trigger"].lower()
            if t["match_type"]=="contains" and n in h: matches.append(t)
            elif t["match_type"]=="exact" and h.strip()==n: matches.append(t)
            elif t["match_type"]=="startswith" and h.startswith(n): matches.append(t)
            elif t["match_type"]=="endswith" and h.endswith(n): matches.append(t)

        if matches:
            embed = success_embed(f"✅ {len(matches)} Match(es) Found", "\n".join(f"• `{t['trigger']}` → {t['response'][:60]}" for t in matches))
        else:
            embed = info_embed("No Matches", f"No auto-responders would fire for: `{message}`")
        await interaction.response.send_message(embed=embed)


class StickyMessages(commands.GroupCog, name="sticky"):
    def __init__(self, bot):
        self.bot = bot

    async def _ensure(self):
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS sticky_messages (
                    channel_id INTEGER PRIMARY KEY,
                    guild_id INTEGER NOT NULL,
                    content TEXT NOT NULL,
                    embed_title TEXT,
                    embed_color TEXT DEFAULT '00D4FF',
                    last_message_id INTEGER,
                    enabled INTEGER DEFAULT 1
                )
            """)
            await db.commit()

    @app_commands.command(name="set", description="Set a sticky message in this channel. It stays at the bottom after every new message.")
    @app_commands.describe(content="Message content", embed_title="Optional embed title", channel="Channel (default: current)")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def set(self, interaction: discord.Interaction, content: str, embed_title: str = None, channel: discord.TextChannel = None):
        await self._ensure()
        ch = channel or interaction.channel
        async with self.bot.db._db_context() as db:
            await db.execute("""
                INSERT OR REPLACE INTO sticky_messages (channel_id, guild_id, content, embed_title, enabled)
                VALUES (?,?,?,?,1)
            """, (ch.id, interaction.guild.id, content, embed_title))
            await db.commit()

        # Send immediately
        if embed_title:
            embed = comprehensive_embed(title=embed_title, description=content, color=XERO.PRIMARY)
            embed.set_footer(text="📌 Sticky Message  •  XERO Bot")
            msg = await ch.send(embed=embed)
        else:
            msg = await ch.send(f"📌 **Sticky:** {content}")

        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE sticky_messages SET last_message_id=? WHERE channel_id=?", (msg.id, ch.id))
            await db.commit()

        await interaction.response.send_message(embed=success_embed("Sticky Set!", f"Sticky message set in {ch.mention}.\nIt will re-post after every new message."))

    @app_commands.command(name="remove", description="Remove the sticky message from a channel.")
    @app_commands.describe(channel="Channel to remove sticky from (default: current)")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def remove(self, interaction: discord.Interaction, channel: discord.TextChannel = None):
        await self._ensure()
        ch = channel or interaction.channel
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT last_message_id FROM sticky_messages WHERE channel_id=?", (ch.id,)) as c:
                row = await c.fetchone()
            if row and row[0]:
                try:
                    old = await ch.fetch_message(row[0])
                    await old.delete()
                except Exception:
                    pass
            await db.execute("DELETE FROM sticky_messages WHERE channel_id=?", (ch.id,))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Sticky Removed", f"Sticky message removed from {ch.mention}."))

    @app_commands.command(name="list", description="View all sticky messages in this server.")
    async def list(self, interaction: discord.Interaction):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT channel_id, content, enabled FROM sticky_messages WHERE guild_id=?", (interaction.guild.id,)) as c:
                rows = await c.fetchall()
        if not rows:
            return await interaction.response.send_message(embed=info_embed("No Stickies", "No sticky messages set. Use `/sticky set` to add one."))
        embed = comprehensive_embed(title=f"📌  Sticky Messages ({len(rows)})", color=XERO.PRIMARY)
        for cid, content, enabled in rows:
            ch = interaction.guild.get_channel(cid)
            embed.add_field(name=f"{'✅' if enabled else '❌'} {ch.name if ch else f'#{cid}'}",
                           value=content[:80], inline=False)
        await interaction.response.send_message(embed=embed)


class Highlights(commands.GroupCog, name="highlight"):
    def __init__(self, bot):
        self.bot = bot

    async def _ensure(self):
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS highlights (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    keyword TEXT NOT NULL,
                    UNIQUE(user_id, guild_id, keyword)
                )
            """)
            await db.commit()

    @app_commands.command(name="add", description="Get DM'd when a keyword is mentioned in this server. Max 10 keywords.")
    @app_commands.describe(keyword="Word or phrase to watch for")
    async def add(self, interaction: discord.Interaction, keyword: str):
        await self._ensure()
        keyword = keyword.lower().strip()
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT COUNT(*) FROM highlights WHERE user_id=? AND guild_id=?", (interaction.user.id, interaction.guild.id)) as c:
                count = (await c.fetchone())[0]
            if count >= 10:
                return await interaction.response.send_message(embed=error_embed("Limit Reached", "You can only highlight 10 keywords per server. Remove one first."), ephemeral=True)
            try:
                await db.execute("INSERT INTO highlights (user_id,guild_id,keyword) VALUES (?,?,?)", (interaction.user.id,interaction.guild.id,keyword))
                await db.commit()
            except aiosqlite.IntegrityError:
                return await interaction.response.send_message(embed=error_embed("Already Added", f"You're already watching `{keyword}`."), ephemeral=True)
        await interaction.response.send_message(embed=success_embed("Highlight Added", f"You'll be DM'd when `{keyword}` is mentioned in this server."))

    @app_commands.command(name="remove", description="Stop watching a keyword.")
    @app_commands.describe(keyword="Keyword to remove")
    async def remove(self, interaction: discord.Interaction, keyword: str):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM highlights WHERE user_id=? AND guild_id=? AND LOWER(keyword)=LOWER(?)", (interaction.user.id,interaction.guild.id,keyword))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Highlight Removed", f"No longer watching `{keyword}`."))

    @app_commands.command(name="list", description="See all your highlight keywords in this server.")
    async def list(self, interaction: discord.Interaction):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT keyword FROM highlights WHERE user_id=? AND guild_id=? ORDER BY keyword", (interaction.user.id,interaction.guild.id)) as c:
                rows = [r[0] for r in await c.fetchall()]
        if not rows:
            return await interaction.response.send_message(embed=info_embed("No Highlights", "You're not watching any keywords. Use `/highlight add` to add one."))
        embed = comprehensive_embed(title="🔔  Your Highlights", description="\n".join(f"• `{kw}`" for kw in rows), color=XERO.PRIMARY)
        embed.set_footer(text=f"{len(rows)}/10 keywords  •  XERO Highlights")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="clear", description="Remove all your highlights in this server.")
    async def clear(self, interaction: discord.Interaction):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM highlights WHERE user_id=? AND guild_id=?", (interaction.user.id,interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Highlights Cleared", "All your highlights for this server removed."))


class Tags(commands.GroupCog, name="tag"):
    def __init__(self, bot):
        self.bot = bot

    async def _ensure(self):
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS tags (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    content TEXT NOT NULL,
                    embed_title TEXT,
                    uses INTEGER DEFAULT 0,
                    created_by INTEGER,
                    UNIQUE(guild_id, name)
                )
            """)
            await db.commit()

    @app_commands.command(name="create", description="Create a tag — a short command that shows a saved message.")
    @app_commands.describe(name="Tag name (no spaces)", content="Tag content", embed_title="Optional embed title")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def create(self, interaction: discord.Interaction, name: str, content: str, embed_title: str = None):
        await self._ensure()
        name = name.lower().replace(" ","-")
        async with self.bot.db._db_context() as db:
            try:
                await db.execute("INSERT INTO tags (guild_id,name,content,embed_title,created_by) VALUES (?,?,?,?,?)", (interaction.guild.id,name,content,embed_title,interaction.user.id))
                await db.commit()
            except aiosqlite.IntegrityError:
                return await interaction.response.send_message(embed=error_embed("Tag Exists", f"A tag named `{name}` already exists. Use `/tag edit` to update it."), ephemeral=True)
        await interaction.response.send_message(embed=success_embed("Tag Created", f"Tag `{name}` created. Use `/tag show {name}` to display it."))

    @app_commands.command(name="show", description="Display a tag by name.")
    @app_commands.describe(name="Tag name to show")
    async def show(self, interaction: discord.Interaction, name: str):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT * FROM tags WHERE guild_id=? AND LOWER(name)=LOWER(?)", (interaction.guild.id, name)) as c:
                tag = await c.fetchone()
        if not tag:
            return await interaction.response.send_message(embed=error_embed("Tag Not Found", f"No tag `{name}`. Use `/tag list` to see all tags."), ephemeral=True)
        # tag = (id, guild_id, name, content, embed_title, uses, created_by)
        if tag[4]:  # embed_title
            embed = comprehensive_embed(title=tag[4], description=tag[3], color=XERO.PRIMARY)
            embed.set_footer(text=f"Tag: {tag[2]}  •  {tag[5]} uses  •  XERO Bot")
            await interaction.response.send_message(embed=embed)
        else:
            await interaction.response.send_message(tag[3])
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE tags SET uses=uses+1 WHERE id=?", (tag[0],))
            await db.commit()

    @app_commands.command(name="list", description="View all tags in this server with usage stats.")
    async def list(self, interaction: discord.Interaction):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT name, uses FROM tags WHERE guild_id=? ORDER BY uses DESC", (interaction.guild.id,)) as c:
                rows = await c.fetchall()
        if not rows:
            return await interaction.response.send_message(embed=info_embed("No Tags", "No tags created. Use `/tag create` to add one."))
        embed = comprehensive_embed(title=f"🏷️  Tags ({len(rows)})", description="Use `/tag show <name>` to display any tag.", color=XERO.PRIMARY)
        for name, uses in rows[:20]:
            embed.add_field(name=f"`{name}`", value=f"{uses} uses", inline=True)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="delete", description="Delete a tag permanently.")
    @app_commands.describe(name="Tag name to delete")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def delete(self, interaction: discord.Interaction, name: str):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM tags WHERE guild_id=? AND LOWER(name)=LOWER(?)", (interaction.guild.id, name))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Tag Deleted", f"Tag `{name}` permanently deleted."))

    @app_commands.command(name="edit", description="Edit an existing tag's content.")
    @app_commands.describe(name="Tag to edit", content="New content", embed_title="New embed title")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def edit(self, interaction: discord.Interaction, name: str, content: str, embed_title: str = None):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE tags SET content=?, embed_title=? WHERE guild_id=? AND LOWER(name)=LOWER(?)", (content, embed_title, interaction.guild.id, name))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Tag Updated", f"Tag `{name}` has been updated."))


async def setup(bot):
    await bot.add_cog(AutoResponder(bot))
    await bot.add_cog(StickyMessages(bot))
    await bot.add_cog(Highlights(bot))
    await bot.add_cog(Tags(bot))
