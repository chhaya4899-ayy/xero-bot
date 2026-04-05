"""
XERO Bot — Profile Extras & Economy Extras
Rep system, marriage, user timezones, transaction history, bank interest.
All with AI — better than MEE6 premium.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, datetime, aiosqlite, asyncio
from utils.embeds import success_embed, error_embed, info_embed, XERO, FOOTER_ECO, FOOTER_MAIN, comprehensive_embed

logger = logging.getLogger("XERO.ProfileExtras")

# Pending marriage proposals: (from_id, guild_id) -> to_id
PROPOSALS: dict = {}


class ProfileExtras(commands.GroupCog, name="rep"):
    def __init__(self, bot):
        self.bot = bot

    async def _ensure_tables(self):
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS reputation (
                    user_id INTEGER, guild_id INTEGER, rep INTEGER DEFAULT 0,
                    last_given TEXT,
                    PRIMARY KEY(user_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS marriages (
                    user1_id INTEGER, user2_id INTEGER, guild_id INTEGER,
                    married_at TEXT,
                    PRIMARY KEY(user1_id, guild_id)
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS user_timezones (
                    user_id INTEGER PRIMARY KEY, timezone TEXT
                )
            """)
            await db.execute("""
                CREATE TABLE IF NOT EXISTS economy_transactions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER, guild_id INTEGER,
                    amount INTEGER, type TEXT, description TEXT,
                    timestamp TEXT DEFAULT (datetime('now'))
                )
            """)
            await db.commit()

    # ── /rep give ─────────────────────────────────────────────────────────
    @app_commands.command(name="give", description="Give someone +1 reputation. Once per day. Shows on their profile.")
    @app_commands.describe(user="Who deserves rep today?", reason="Why you're giving them rep (optional)")
    async def give(self, interaction: discord.Interaction, user: discord.Member, reason: str = ""):
        await self._ensure_tables()
        if user.id == interaction.user.id:
            return await interaction.response.send_message(embed=error_embed("Nice Try", "You can't give yourself rep. Earn it."), ephemeral=True)
        if user.bot:
            return await interaction.response.send_message(embed=error_embed("Bots Don't Need Rep", "Give rep to real people!"), ephemeral=True)

        now = datetime.datetime.now(datetime.timezone.utc)
        async with self.bot.db._db_context() as db:
            # Check giver's cooldown
            async with db.execute(
                "SELECT last_given FROM reputation WHERE user_id=? AND guild_id=?",
                (interaction.user.id, interaction.guild.id)
            ) as c:
                giver_row = await c.fetchone()

            if giver_row and giver_row[0]:
                last = datetime.datetime.fromisoformat(giver_row[0])
                if last.tzinfo is None: last = last.replace(tzinfo=datetime.timezone.utc)
                if (now - last).total_seconds() < 86400:
                    next_ts = int((last + datetime.timedelta(days=1)).timestamp())
                    return await interaction.response.send_message(embed=error_embed(
                        "Already Given Today",
                        f"You can give rep again <t:{next_ts}:R>.\n*One rep per day — make it count.*"
                    ))

            # Give rep
            await db.execute(
                "INSERT INTO reputation (user_id, guild_id, rep) VALUES (?,?,1) ON CONFLICT(user_id,guild_id) DO UPDATE SET rep=rep+1",
                (user.id, interaction.guild.id)
            )
            await db.execute(
                "INSERT INTO reputation (user_id, guild_id, last_given) VALUES (?,?,?) ON CONFLICT(user_id,guild_id) DO UPDATE SET last_given=?",
                (interaction.user.id, interaction.guild.id, now.isoformat(), now.isoformat())
            )
            async with db.execute("SELECT rep FROM reputation WHERE user_id=? AND guild_id=?", (user.id, interaction.guild.id)) as c:
                new_rep = (await c.fetchone())[0]
            await db.commit()

        embed = discord.Embed(
            title="⭐  Rep Given!",
            description=f"{interaction.user.mention} gave **+1 rep** to {user.mention}!",
            color=XERO.GOLD
        )
        embed.set_thumbnail(url=user.display_avatar.url)
        embed.add_field(name="⭐ New Rep", value=f"**{new_rep}**", inline=True)
        if reason: embed.add_field(name="💬 Reason", value=reason, inline=True)
        embed.set_footer(text="XERO Rep System  •  One rep per day")
        await interaction.response.send_message(embed=embed)

    # ── /rep check ────────────────────────────────────────────────────────
    @app_commands.command(name="check", description="Check how much reputation someone has.")
    @app_commands.describe(user="User to check (default: yourself)")
    async def check(self, interaction: discord.Interaction, user: discord.Member = None):
        await self._ensure_tables()
        target = user or interaction.user
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT rep FROM reputation WHERE user_id=? AND guild_id=?", (target.id, interaction.guild.id)) as c:
                row = await c.fetchone()
            async with db.execute("SELECT COUNT(*)+1 FROM reputation WHERE guild_id=? AND rep>(SELECT COALESCE(rep,0) FROM reputation WHERE user_id=? AND guild_id=?)", (interaction.guild.id, target.id, interaction.guild.id)) as c:
                rank = (await c.fetchone())[0]

        rep = row[0] if row else 0
        bar = "⭐" * min(rep, 10) + "☆" * max(0, 10-rep)
        embed = comprehensive_embed(title=f"⭐  {target.display_name}'s Reputation", color=XERO.GOLD)
        embed.set_thumbnail(url=target.display_avatar.url)
        embed.add_field(name="⭐ Total Rep", value=f"**{rep}**", inline=True)
        embed.add_field(name="🏆 Server Rank", value=f"**#{rank}**", inline=True)
        embed.add_field(name="📊 Visual", value=bar, inline=False)
        embed.set_footer(text="XERO Rep System  •  /rep give @user to give rep")
        await interaction.response.send_message(embed=embed)

    # ── /rep leaderboard ──────────────────────────────────────────────────
    @app_commands.command(name="leaderboard", description="See the most reputable members in this server.")
    async def leaderboard(self, interaction: discord.Interaction):
        await self._ensure_tables()
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT user_id, rep FROM reputation WHERE guild_id=? ORDER BY rep DESC LIMIT 10", (interaction.guild.id,)) as c:
                rows = await c.fetchall()
        if not rows:
            return await interaction.response.send_message(embed=info_embed("No Rep Yet", "Nobody has rep yet! Use `/rep give @user` to start."))
        medals = ["🥇","🥈","🥉"] + [f"#{i}" for i in range(4,11)]
        embed = comprehensive_embed(title="⭐  Reputation Leaderboard", color=XERO.GOLD)
        desc = ""
        for i,(uid,rep) in enumerate(rows):
            m = interaction.guild.get_member(uid)
            name = m.display_name if m else f"User {uid}"
            desc += f"{medals[i]} **{name}** — {rep} ⭐\n"
        embed.description = desc
        embed.set_footer(text="XERO Rep System  •  /rep give @user")
        await interaction.response.send_message(embed=embed)


class MarriageSystem(commands.GroupCog, name="marry"):
    def __init__(self, bot):
        self.bot = bot

    async def _ensure_tables(self):
        async with self.bot.db._db_context() as db:
            await db.execute("""
                CREATE TABLE IF NOT EXISTS marriages (
                    user1_id INTEGER NOT NULL, user2_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL, married_at TEXT,
                    PRIMARY KEY(user1_id, guild_id)
                )
            """)
            await db.commit()

    async def _get_partner(self, user_id: int, guild_id: int):
        async with self.bot.db._db_context() as db:
            async with db.execute(
                "SELECT user1_id, user2_id FROM marriages WHERE (user1_id=? OR user2_id=?) AND guild_id=?",
                (user_id, user_id, guild_id)
            ) as c:
                row = await c.fetchone()
        if not row: return None
        return row[1] if row[0] == user_id else row[0]

    @app_commands.command(name="propose", description="Propose to someone! They have 60 seconds to accept.")
    @app_commands.describe(user="Who to propose to")
    async def propose(self, interaction: discord.Interaction, user: discord.Member):
        await self._ensure_tables()
        if user.id == interaction.user.id:
            return await interaction.response.send_message(embed=error_embed("Self-love is great", "But you can't marry yourself."), ephemeral=True)
        if user.bot:
            return await interaction.response.send_message(embed=error_embed("Bots Can't Marry", "Find a real person!"), ephemeral=True)

        # Check if already married
        my_partner    = await self._get_partner(interaction.user.id, interaction.guild.id)
        their_partner = await self._get_partner(user.id, interaction.guild.id)
        if my_partner:
            return await interaction.response.send_message(embed=error_embed("Already Married", f"You're already married to <@{my_partner}>. Divorce first with `/marry divorce`."), ephemeral=True)
        if their_partner:
            return await interaction.response.send_message(embed=error_embed("Taken", f"{user.mention} is already married to <@{their_partner}>."), ephemeral=True)

        # Send proposal
        PROPOSALS[(interaction.user.id, interaction.guild.id)] = user.id
        embed = discord.Embed(
            title="💍  Marriage Proposal!",
            description=(
                f"{interaction.user.mention} is proposing to {user.mention}!\n\n"
                f"**{user.display_name}**, do you accept?\n"
                f"*You have 60 seconds to respond.*"
            ),
            color=XERO.SECONDARY
        )
        embed.set_thumbnail(url=interaction.user.display_avatar.url)
        embed.set_footer(text="XERO Marriage System  •  💍")
        view = ProposalView(self.bot, interaction.user, user)
        await interaction.response.send_message(embed=embed, view=view)

    @app_commands.command(name="status", description="Check your or someone's marriage status.")
    @app_commands.describe(user="User to check (default: yourself)")
    async def status(self, interaction: discord.Interaction, user: discord.Member = None):
        await self._ensure_tables()
        target = user or interaction.user
        partner_id = await self._get_partner(target.id, interaction.guild.id)
        if not partner_id:
            msg = f"{'You are' if target==interaction.user else f'{target.display_name} is'} single. 💔"
            return await interaction.response.send_message(embed=info_embed("Relationship Status", msg))
        partner = interaction.guild.get_member(partner_id)
        async with self.bot.db._db_context() as db:
            async with db.execute(
                "SELECT married_at FROM marriages WHERE (user1_id=? OR user2_id=?) AND guild_id=?",
                (target.id, target.id, interaction.guild.id)
            ) as c:
                row = await c.fetchone()
        married_at = row[0] if row else None
        embed = comprehensive_embed(title=f"💍  {target.display_name}'s Relationship", color=XERO.SECONDARY)
        embed.set_thumbnail(url=target.display_avatar.url)
        embed.add_field(name="💑 Partner", value=partner.mention if partner else f"<@{partner_id}>", inline=True)
        if married_at:
            ts = int(datetime.datetime.fromisoformat(married_at).timestamp())
            embed.add_field(name="📅 Married", value=f"<t:{ts}:D> (<t:{ts}:R>)", inline=True)
        embed.set_footer(text="XERO Marriage System  •  💍")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="divorce", description="End your marriage. This is permanent and immediate.")
    async def divorce(self, interaction: discord.Interaction):
        await self._ensure_tables()
        partner_id = await self._get_partner(interaction.user.id, interaction.guild.id)
        if not partner_id:
            return await interaction.response.send_message(embed=error_embed("Not Married", "You're not married. Nothing to divorce."), ephemeral=True)
        async with self.bot.db._db_context() as db:
            await db.execute(
                "DELETE FROM marriages WHERE (user1_id=? OR user2_id=?) AND guild_id=?",
                (interaction.user.id, interaction.user.id, interaction.guild.id)
            )
            await db.commit()
        await interaction.response.send_message(embed=info_embed("Divorced 💔", f"Your marriage with <@{partner_id}> has ended."))


class ProposalView(discord.ui.View):
    def __init__(self, bot, proposer, target):
        super().__init__(timeout=60)
        self.bot      = bot
        self.proposer = proposer
        self.target   = target

    @discord.ui.button(label="💍 Accept", style=discord.ButtonStyle.success)
    async def accept(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.target.id:
            return await interaction.response.send_message("Only the person being proposed to can accept!")
        now = datetime.datetime.now(datetime.timezone.utc).isoformat()
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO marriages (user1_id, user2_id, guild_id, married_at) VALUES (?,?,?,?)",
                (self.proposer.id, self.target.id, interaction.guild.id, now)
            )
            await db.commit()
        embed = discord.Embed(
            title="💍  They Said YES!",
            description=f"🎊 {self.proposer.mention} and {self.target.mention} are now **married**!\n*Congratulations to the happy couple!*",
            color=XERO.GOLD
        )
        embed.set_footer(text="XERO Marriage System  •  💍")
        await interaction.response.edit_message(embed=embed, view=None)

    @discord.ui.button(label="💔 Decline", style=discord.ButtonStyle.danger)
    async def decline(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.target.id:
            return await interaction.response.send_message("Only the person being proposed to can decline!")
        embed = discord.Embed(
            title="💔  Proposal Declined",
            description=f"{self.target.mention} declined the proposal from {self.proposer.mention}.\n*There are plenty of fish in the sea...*",
            color=XERO.ERROR
        )
        await interaction.response.edit_message(embed=embed, view=None)


class EconomyExtras(commands.Cog):
    """Economy extensions: transaction log, bank interest, user timezone."""
    def __init__(self, bot):
        self.bot = bot
        self.apply_bank_interest.start()

    def cog_unload(self):
        self.apply_bank_interest.cancel()

    @discord.ext.tasks.loop(hours=24)
    async def apply_bank_interest(self):
        """0.5% daily interest on all banked money."""
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute("SELECT user_id, guild_id, bank FROM economy WHERE bank > 100") as c:
                    rows = await c.fetchall()
                for user_id, guild_id, bank in rows:
                    interest = max(1, int(bank * 0.005))
                    await db.execute(
                        "UPDATE economy SET bank=bank+?, total_earned=total_earned+? WHERE user_id=? AND guild_id=?",
                        (interest, interest, user_id, guild_id)
                    )
                await db.commit()
            logger.info(f"✓ Bank interest applied to {len(rows)} accounts")
        except Exception as e:
            logger.error(f"Bank interest: {e}")

    @apply_bank_interest.before_loop
    async def before_interest(self): await self.bot.wait_until_ready()

    async def log_transaction(self, user_id, guild_id, amount, type_, desc):
        try:
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "CREATE TABLE IF NOT EXISTS economy_transactions (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, guild_id INTEGER, amount INTEGER, type TEXT, description TEXT, timestamp TEXT DEFAULT (datetime('now')))"
                )
                await db.execute(
                    "INSERT INTO economy_transactions (user_id, guild_id, amount, type, description) VALUES (?,?,?,?,?)",
                    (user_id, guild_id, amount, type_, desc)
                )
                await db.commit()
        except Exception as e:
            logger.debug(f"Transaction log: {e}")

    @app_commands.command(name="history", description="View your last 20 economy transactions — every earn, spend, and transfer.")  # type: ignore
    @app_commands.describe(user="User to check (default: yourself)")
    async def history(self, interaction: discord.Interaction, user: discord.Member = None):
        target = user or interaction.user
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT amount, type, description, timestamp FROM economy_transactions WHERE user_id=? AND guild_id=? ORDER BY id DESC LIMIT 20",
                    (target.id, interaction.guild.id)
                ) as c:
                    rows = await c.fetchall()
        except Exception:
            rows = []

        if not rows:
            return await interaction.response.send_message(embed=info_embed(
                "No Transaction History",
                f"No transactions recorded for {target.mention if target != interaction.user else 'you'} yet.\n"
                f"*Start earning with `/economy work`, `/daily`, and more!*"
            ))

        embed = comprehensive_embed(
            title=f"📋  Transaction History — {target.display_name}",
            description=f"Last {len(rows)} transactions",
            color=XERO.ECONOMY if hasattr(XERO,'ECONOMY') else XERO.SUCCESS,
            thumbnail_url=target.display_avatar.url
        )
        desc = ""
        for amount, type_, description, ts in rows:
            try:
                dt = datetime.datetime.fromisoformat(ts)
                time_str = f"<t:{int(dt.timestamp())}:R>"
            except Exception:
                time_str = ts[:10] if ts else "?"
            arrow = "📈" if amount >= 0 else "📉"
            sign  = "+" if amount >= 0 else ""
            desc += f"{arrow} **{sign}${amount:,}** — {description or type_} {time_str}\n"
        embed.description = desc[:2000]
        embed.set_footer(text="XERO Economy  •  Full transaction history")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="timezone", description="Set your timezone for accurate reminder times and timestamps.")  # type: ignore
    @app_commands.describe(timezone="Your timezone (e.g. US/Eastern, Europe/London, Asia/Tokyo)")
    async def timezone(self, interaction: discord.Interaction, timezone: str):
        # Validate
        import zoneinfo
        try:
            zoneinfo.ZoneInfo(timezone)
        except Exception:
            common = ["US/Eastern", "US/Central", "US/Mountain", "US/Pacific", "Europe/London", "Europe/Paris", "Europe/Berlin", "Asia/Tokyo", "Asia/Dubai", "Australia/Sydney", "UTC"]
            return await interaction.response.send_message(embed=error_embed(
                "Invalid Timezone",
                f"`{timezone}` is not a valid timezone.\n\n**Common timezones:**\n" + "\n".join(f"`{tz}`" for tz in common)
            ))
        async with self.bot.db._db_context() as db:
            await db.execute(
                "CREATE TABLE IF NOT EXISTS user_timezones (user_id INTEGER PRIMARY KEY, timezone TEXT)"
            )
            await db.execute(
                "INSERT OR REPLACE INTO user_timezones (user_id, timezone) VALUES (?,?)",
                (interaction.user.id, timezone)
            )
            await db.commit()
        import zoneinfo, datetime as dt
        now_local = dt.datetime.now(zoneinfo.ZoneInfo(timezone))
        await interaction.response.send_message(embed=success_embed(
            "Timezone Set!",
            f"**Timezone:** `{timezone}`\n"
            f"**Current time for you:** `{now_local.strftime('%H:%M, %A %B %d')}`\n\n"
            f"*Reminders will now fire at your local time.*"
        ))


async def setup(bot):
    await bot.add_cog(ProfileExtras(bot))
    await bot.add_cog(MarriageSystem(bot))
    await bot.add_cog(EconomyExtras(bot))
