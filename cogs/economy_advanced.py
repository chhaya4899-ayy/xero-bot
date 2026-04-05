"""
XERO Bot — Living Economy Advanced (14 commands)
Streaks, heists, stock market, crafting, daily events.
This is what keeps members coming back every single day.
"""
import discord
from discord.ext import commands, tasks
from discord import app_commands
import logging
import random
import datetime
import asyncio
import aiosqlite
from utils.embeds import (
    success_embed, error_embed, info_embed, comprehensive_embed,
    heist_embed, stock_embed, XERO, FOOTER_ECO
)

logger = logging.getLogger("XERO.EcoAdvanced")

# Active heist trackers: guild_id -> heist state
ACTIVE_HEISTS: dict = {}

# Daily server events (chosen randomly each day)
DAILY_EVENTS = [
    {"name": "💹 Bull Market",      "desc": "Stock prices surge today! +20% on all buys.",     "type": "bull_market"},
    {"name": "📉 Bear Market",      "desc": "Stock prices crash today! Sell before it's late.", "type": "bear_market"},
    {"name": "🎰 Lucky Hours",      "desc": "Slot multipliers doubled for the next hour!",      "type": "lucky_slots"},
    {"name": "💼 Overtime Pay",     "desc": "Work pays 2× today!",                              "type": "double_work"},
    {"name": "🏦 Bank Holiday",     "desc": "All deposits are free today!",                     "type": "bank_holiday"},
    {"name": "🎁 Community Drop",   "desc": "Free $2,500 for anyone who claims with /claim!",   "type": "community_drop"},
    {"name": "⚡ XP Surge",         "desc": "Earn 3× XP from messages for the next 2 hours!",  "type": "xp_surge"},
    {"name": "💎 Heist Bonus",      "desc": "Heist payouts are 50% higher today!",              "type": "heist_bonus"},
]

# Current active daily event per guild: guild_id -> event
ACTIVE_EVENTS: dict = {}

BANKS = [
    "First National Bank",   "City Credit Union",     "Diamond Vault",
    "Royal Reserve Bank",    "Federal Treasury",      "Crypto Exchange",
    "Silicon Valley Bank",   "Offshore Cayman Fund",  "Central Bank",
]


class EconomyAdvanced(commands.Cog):
    def __init__(self, bot):
        self.bot = bot
        self.update_stocks.start()
        self.cycle_daily_event.start()

    def cog_unload(self):
        self.update_stocks.cancel()
        self.cycle_daily_event.cancel()

    # ── Background: Update stock prices every hour ────────────────────────
    @tasks.loop(hours=1)
    async def update_stocks(self):
        try:
            stocks = await self.bot.db.get_stocks()
            for s in stocks:
                # Random walk with mean reversion
                volatility = s["volatility"]
                base = s["price"]
                change_pct = random.gauss(0, volatility) * 0.5
                # Mean reversion toward ~1000
                mean_rev = (1000 - base) * 0.01
                new_price = int(base * (1 + change_pct) + mean_rev)
                new_price = max(10, min(9999, new_price))
                await self.bot.db.update_stock_price(s["symbol"], new_price, base)
            logger.info("✓ Stock prices updated")
        except Exception as e:
            logger.error(f"Stock update error: {e}")

    @update_stocks.before_loop
    async def before_stocks(self):
        await self.bot.wait_until_ready()

    # ── Background: Cycle daily event ─────────────────────────────────────
    @tasks.loop(hours=6)
    async def cycle_daily_event(self):
        try:
            event = random.choice(DAILY_EVENTS)
            for guild in self.bot.guilds:
                ACTIVE_EVENTS[guild.id] = event
                settings = await self.bot.db.get_guild_settings(guild.id)
                channel_id = settings.get("log_channel_id") or settings.get("welcome_channel_id")
                if not channel_id:
                    continue
                channel = guild.get_channel(channel_id)
                if not channel:
                    continue
                try:
                    embed = discord.Embed(
                        title=f"🌟  SERVER EVENT: {event['name']}",
                        description=f"{event['desc']}\n\n*This event lasts 6 hours!*",
                        color=XERO.GOLD
                    )
                    embed.set_footer(text="XERO Economy  •  Daily Events")
                    await channel.send(embed=embed)
                except Exception:
                    pass
        except Exception as e:
            logger.error(f"Daily event error: {e}")

    @cycle_daily_event.before_loop
    async def before_event(self):
        await self.bot.wait_until_ready()

    def _get_streak_multiplier(self, streak: int) -> float:
        """Streak multipliers: 1 day=1×, 3=1.25×, 7=1.5×, 14=2×, 30=3×"""
        if streak >= 30: return 3.0
        if streak >= 14: return 2.0
        if streak >= 7:  return 1.5
        if streak >= 3:  return 1.25
        return 1.0

    # ── /daily (enhanced with streaks) ────────────────────────────────────
    @app_commands.command(name="daily", description="Claim your daily reward. Build streaks for massive multipliers!")
    async def daily(self, interaction: discord.Interaction):
        data   = await self.bot.db.get_economy(interaction.user.id, interaction.guild.id)
        streak = await self.bot.db.get_streak(interaction.user.id, interaction.guild.id)
        today  = datetime.date.today().isoformat()
        last   = streak.get("last_daily_date")

        # Check cooldown
        if last == today:
            tomorrow = datetime.datetime.combine(datetime.date.today() + datetime.timedelta(days=1), datetime.time())
            ts = int(tomorrow.timestamp())
            s  = streak.get("daily_streak", 0)
            mult = self._get_streak_multiplier(s)
            return await interaction.response.send_message(embed=error_embed(
                "Already Claimed!",
                f"Next daily: <t:{ts}:R>\n\n"
                f"🔥 **Current Streak:** {s} days\n"
                f"⚡ **Multiplier:** {mult}×\n"
                f"💎 **Best Streak:** {streak.get('best_streak',0)} days"
            ))

        # Update streak
        yesterday = (datetime.date.today() - datetime.timedelta(days=1)).isoformat()
        curr_streak = streak.get("daily_streak", 0)
        new_streak  = (curr_streak + 1) if last == yesterday else 1
        await self.bot.db.update_streak(interaction.user.id, interaction.guild.id, new_streak, today)

        # Calculate reward
        base   = 5000
        mult   = self._get_streak_multiplier(new_streak)
        bonus  = random.randint(0, 2000)
        event  = ACTIVE_EVENTS.get(interaction.guild.id)
        if event and event.get("type") == "double_work":
            mult *= 2
        total  = int((base + bonus) * mult)

        await self.bot.db.update_economy(interaction.user.id, interaction.guild.id, wallet_delta=total, earned_delta=total)
        await self.bot.db.set_economy_timestamp(interaction.user.id, interaction.guild.id, "last_daily", datetime.datetime.now().isoformat())

        streak_bar = "🔥" * min(new_streak, 10)
        embed = discord.Embed(
            title="🎁  Daily Reward Claimed!",
            color=XERO.SUCCESS if new_streak < 7 else XERO.GOLD
        )
        embed.add_field(name="💰  Reward",       value=f"**${total:,}**",          inline=True)
        embed.add_field(name="⚡  Multiplier",   value=f"**{mult}×**",              inline=True)
        embed.add_field(name="🔥  Streak",       value=f"**{new_streak} days**",    inline=True)
        embed.add_field(name="📊  Breakdown",    value=f"Base: ${base:,} + Bonus: ${bonus:,} × {mult}", inline=False)
        if new_streak > 1:
            embed.add_field(name="🏆  Streak Progress", value=f"{streak_bar}\n*Next milestone:* {'30 days (3×)' if new_streak<30 else '14 days (2×)' if new_streak<14 else '7 days (1.5×)' if new_streak<7 else '✅ Max!'}", inline=False)
        if event:
            embed.add_field(name=f"🌟  Active Event: {event['name']}", value=event["desc"], inline=False)
        if new_streak % 7 == 0 and new_streak > 0:
            embed.description = f"🎊 **WEEK {new_streak//7} COMPLETE!** You're on fire!"
        embed.set_thumbnail(url=interaction.user.display_avatar.url)
        embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    # ── /streak ────────────────────────────────────────────────────────────
    @app_commands.command(name="streak", description="View your current daily streak, best streak, and multiplier breakdown.")
    @app_commands.describe(user="User to check (default: yourself)")
    async def streak(self, interaction: discord.Interaction, user: discord.Member = None):
        target = user or interaction.user
        streak = await self.bot.db.get_streak(target.id, interaction.guild.id)
        curr   = streak.get("daily_streak", 0)
        best   = streak.get("best_streak", 0)
        mult   = self._get_streak_multiplier(curr)

        milestones = [(3, 1.25, "1.25×"), (7, 1.5, "1.5×"), (14, 2.0, "2×"), (30, 3.0, "3×")]
        next_ms = next(((d, l) for d, m, l in milestones if curr < d), None)

        embed = discord.Embed(
            title=f"🔥  {target.display_name}'s Daily Streak",
            color=XERO.GOLD if curr >= 7 else XERO.PRIMARY
        )
        embed.set_thumbnail(url=target.display_avatar.url)
        embed.add_field(name="🔥  Current Streak",  value=f"**{curr} days**",                       inline=True)
        embed.add_field(name="🏆  Best Streak",     value=f"**{best} days**",                        inline=True)
        embed.add_field(name="⚡  Multiplier",      value=f"**{mult}×** daily reward",               inline=True)
        if next_ms:
            days_left, label = next_ms
            embed.add_field(name="🎯  Next Milestone", value=f"**{days_left - curr}** more days → **{label}** multiplier", inline=False)
        else:
            embed.add_field(name="👑  Status", value="**MAX MULTIPLIER** — 3× daily reward!", inline=False)
        bar = "🔥" * min(curr, 10) + "⬜" * (10 - min(curr, 10))
        embed.add_field(name="📊  Streak Bar", value=bar, inline=False)
        embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    # ── /heist ─────────────────────────────────────────────────────────────
    @app_commands.command(name="heist", description="Start a group bank heist! Recruit crew members for a better shot at success.")
    @app_commands.describe(target="Bank to rob (leave blank for random)")
    async def heist(self, interaction: discord.Interaction, target: str = None):
        # Check for active heist
        if interaction.guild.id in ACTIVE_HEISTS:
            existing = ACTIVE_HEISTS[interaction.guild.id]
            return await interaction.response.send_message(embed=error_embed(
                "Heist Already Active",
                f"There's already a heist in progress in {interaction.guild.get_channel(existing['channel_id']).mention}!\n"
                f"Join it or wait for it to finish."
            ))

        # Check leader has enough money to risk
        data = await self.bot.db.get_economy(interaction.user.id, interaction.guild.id)
        if data["wallet"] < 500:
            return await interaction.response.send_message(embed=error_embed(
                "Not Enough Cash",
                "You need at least **$500** in your wallet to plan a heist. Get that bread first."
            ))

        bank        = target or random.choice(BANKS)
        potential   = random.randint(15_000, 75_000)
        event       = ACTIVE_EVENTS.get(interaction.guild.id)
        if event and event.get("type") == "heist_bonus":
            potential = int(potential * 1.5)

        # Register heist
        ACTIVE_HEISTS[interaction.guild.id] = {
            "leader_id":    interaction.user.id,
            "channel_id":   interaction.channel.id,
            "target":       bank,
            "potential":    potential,
            "participants": [interaction.user],
        }

        embed = heist_embed(interaction.user, bank, [interaction.user], potential)
        view  = HeistJoinView(self.bot, interaction.guild.id)
        msg   = await interaction.response.send_message(embed=embed, view=view)

        # Auto-execute after 60 seconds
        await asyncio.sleep(60)
        if interaction.guild.id in ACTIVE_HEISTS:
            await self._execute_heist(interaction.guild, interaction.channel)

    async def _execute_heist(self, guild: discord.Guild, channel: discord.TextChannel):
        if guild.id not in ACTIVE_HEISTS:
            return
        state        = ACTIVE_HEISTS.pop(guild.id)
        participants = state["participants"]
        potential    = state["potential"]
        bank         = state["target"]

        # Success chance: 30% base + 5% per extra crew member (max 80%)
        success_pct = min(0.30 + (len(participants) - 1) * 0.08, 0.80)
        success     = random.random() < success_pct

        if success:
            actual = int(potential * random.uniform(0.6, 1.0))
            per_p  = actual // len(participants)
            for m in participants:
                await self.bot.db.update_economy(m.id, guild.id, wallet_delta=per_p, earned_delta=per_p)
            embed = heist_embed(participants[0], bank, participants, potential, success=True, actual_reward=actual)
        else:
            fine = random.randint(300, 800)
            for m in participants:
                data = await self.bot.db.get_economy(m.id, guild.id)
                actual_fine = min(fine, data["wallet"])
                await self.bot.db.update_economy(m.id, guild.id, wallet_delta=-actual_fine, spent_delta=actual_fine)
            embed = heist_embed(participants[0], bank, participants, potential, success=False, actual_reward=fine)

        mentions = " ".join(m.mention for m in participants)
        try:
            await channel.send(content=mentions, embed=embed)
        except Exception as e:
            logger.error(f"Heist result send error: {e}")

    # ── /stock market ──────────────────────────────────────────────────────
    @app_commands.command(name="stocks", description="View the XERO Stock Exchange — live prices, changes, and your portfolio value.")
    async def stocks_view(self, interaction: discord.Interaction):
        all_stocks = await self.bot.db.get_stocks()
        embed = stock_embed(all_stocks)
        embed.add_field(name="💡  How to Trade", value="`/buy-stock SYMBOL SHARES` • `/sell-stock SYMBOL SHARES` • `/portfolio` to view holdings", inline=False)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="buy-stock", description="Buy shares of a stock from the XERO exchange.")
    @app_commands.describe(symbol="Stock ticker (e.g. XERO, NVDA, MEME)", shares="Number of shares to buy")
    async def buy_stock(self, interaction: discord.Interaction, symbol: str, shares: int):
        symbol = symbol.upper()
        if shares <= 0:
            return await interaction.response.send_message(embed=error_embed("Invalid", "Shares must be positive."), ephemeral=True)

        stocks = await self.bot.db.get_stocks()
        stock  = next((s for s in stocks if s["symbol"] == symbol), None)
        if not stock:
            syms = ", ".join(f"`{s['symbol']}`" for s in stocks)
            return await interaction.response.send_message(embed=error_embed("Stock Not Found", f"No stock `{symbol}`. Available: {syms}"), ephemeral=True)

        # Bull market event bonus
        price = stock["price"]
        event = ACTIVE_EVENTS.get(interaction.guild.id)
        total_cost = price * shares

        data = await self.bot.db.get_economy(interaction.user.id, interaction.guild.id)
        if total_cost > data["wallet"]:
            return await interaction.response.send_message(embed=error_embed(
                "Insufficient Funds",
                f"**{shares}× {symbol}** costs **${total_cost:,}** but you only have **${data['wallet']:,}** in your wallet."
            ))

        await self.bot.db.update_economy(interaction.user.id, interaction.guild.id, wallet_delta=-total_cost, spent_delta=total_cost)
        await self.bot.db.buy_stock(interaction.user.id, interaction.guild.id, symbol, shares, price)

        embed = success_embed(
            f"Purchased {shares}× {symbol}",
            f"Bought **{shares} share(s)** of **{stock['name']}** at **${price:,}/share**\n"
            f"**Total cost:** ${total_cost:,}\n"
            f"**Remaining wallet:** ${data['wallet'] - total_cost:,}"
        )
        embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="sell-stock", description="Sell shares from your portfolio.")
    @app_commands.describe(symbol="Stock ticker", shares="Number of shares to sell")
    async def sell_stock(self, interaction: discord.Interaction, symbol: str, shares: int):
        symbol = symbol.upper()
        if shares <= 0:
            return await interaction.response.send_message(embed=error_embed("Invalid", "Shares must be positive."), ephemeral=True)

        portfolio = await self.bot.db.get_portfolio(interaction.user.id, interaction.guild.id)
        holding   = next((h for h in portfolio if h["symbol"] == symbol), None)
        if not holding:
            return await interaction.response.send_message(embed=error_embed("Not Owned", f"You don't own any **{symbol}** shares. Check `/portfolio`."), ephemeral=True)
        if holding["shares"] < shares:
            return await interaction.response.send_message(embed=error_embed(
                "Not Enough Shares",
                f"You only own **{holding['shares']}** share(s) of **{symbol}**."
            ))

        price    = holding["price"]
        proceeds = price * shares
        profit   = (price - holding["avg_buy_price"]) * shares

        success = await self.bot.db.sell_stock(interaction.user.id, interaction.guild.id, symbol, shares)
        if not success:
            return await interaction.response.send_message(embed=error_embed("Error", "Sale failed. Try again."), ephemeral=True)

        await self.bot.db.update_economy(interaction.user.id, interaction.guild.id, wallet_delta=proceeds, earned_delta=max(0, profit))

        profit_str = f"+${profit:,} 📈" if profit >= 0 else f"-${abs(profit):,} 📉"
        embed = success_embed(
            f"Sold {shares}× {symbol}",
            f"Sold **{shares} share(s)** of **{symbol}** at **${price:,}/share**\n"
            f"**Proceeds:** ${proceeds:,}\n"
            f"**Profit/Loss:** {profit_str}\n"
            f"**Avg Buy Price:** ${holding['avg_buy_price']:,}"
        )
        embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="portfolio", description="View your stock portfolio — holdings, value, profit/loss.")
    @app_commands.describe(user="User to check (default: yourself)")
    async def portfolio(self, interaction: discord.Interaction, user: discord.Member = None):
        target    = user or interaction.user
        portfolio = await self.bot.db.get_portfolio(target.id, interaction.guild.id)
        if not portfolio:
            return await interaction.response.send_message(embed=info_embed(
                "Empty Portfolio",
                f"{'You have' if target == interaction.user else f'{target.display_name} has'} no stock holdings.\n"
                f"Use `/stocks` to see available stocks and `/buy-stock` to invest!"
            ))

        total_value  = sum(h["shares"] * h["price"] for h in portfolio)
        total_cost   = sum(h["shares"] * h["avg_buy_price"] for h in portfolio)
        total_profit = total_value - total_cost

        embed = discord.Embed(
            title=f"📈  {target.display_name}'s Portfolio",
            color=XERO.SUCCESS if total_profit >= 0 else XERO.DANGER
        )
        embed.set_thumbnail(url=target.display_avatar.url)

        for h in portfolio:
            value  = h["shares"] * h["price"]
            cost   = h["shares"] * h["avg_buy_price"]
            pl     = value - cost
            pl_str = f"+${pl:,} 📈" if pl >= 0 else f"-${abs(pl):,} 📉"
            change_pct = (h["price"] - h["avg_buy_price"]) / max(h["avg_buy_price"], 1) * 100
            embed.add_field(
                name=f"**{h['symbol']}**  •  {h['shares']} shares",
                value=f"Value: **${value:,}**  |  P/L: **{pl_str}**\nCurrent: ${h['price']:,}  |  Avg Buy: ${h['avg_buy_price']:,}  ({change_pct:+.1f}%)",
                inline=False
            )

        profit_str = f"+${total_profit:,} 📈" if total_profit >= 0 else f"-${abs(total_profit):,} 📉"
        embed.add_field(name="💰  Total Portfolio Value", value=f"**${total_value:,}**", inline=True)
        embed.add_field(name="📊  Total P/L",             value=f"**{profit_str}**",    inline=True)
        embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    # ── /event ─────────────────────────────────────────────────────────────
    @app_commands.command(name="event", description="Check the current active server economy event and its bonuses.")
    async def event(self, interaction: discord.Interaction):
        event = ACTIVE_EVENTS.get(interaction.guild.id)
        if not event:
            return await interaction.response.send_message(embed=info_embed(
                "No Active Event",
                "No economy event is active right now. Events run automatically every 6 hours!"
            ))
        embed = discord.Embed(
            title=f"🌟  Active Event: {event['name']}",
            description=event["desc"],
            color=XERO.GOLD
        )
        embed.set_footer(text="XERO Economy  •  Events rotate every 6 hours")
        await interaction.response.send_message(embed=embed)

    # ── /craft ─────────────────────────────────────────────────────────────
    @app_commands.command(name="craft", description="Combine two shop items to craft a more valuable item.")
    @app_commands.describe(item1="First item name", item2="Second item name")
    async def craft(self, interaction: discord.Interaction, item1: str, item2: str):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            # Find matching recipe (order-independent)
            async with db.execute("""
                SELECT * FROM craft_recipes WHERE guild_id=?
                AND ((LOWER(ingredient1)=LOWER(?) AND LOWER(ingredient2)=LOWER(?))
                  OR (LOWER(ingredient1)=LOWER(?) AND LOWER(ingredient2)=LOWER(?)))
            """, (interaction.guild.id, item1, item2, item2, item1)) as c:
                recipe = await c.fetchone()

        if not recipe:
            return await interaction.response.send_message(embed=error_embed(
                "No Recipe Found",
                f"No crafting recipe found for **{item1}** + **{item2}**.\n"
                f"Admins can add recipes with `/craft-add`."
            ))

        recipe = dict(recipe)
        # Check user owns both items
        async with self.bot.db._db_context() as db:
            for item_name in [item1, item2]:
                async with db.execute(
                    "SELECT quantity FROM economy_inventory WHERE user_id=? AND guild_id=? AND LOWER(item_name)=LOWER(?) AND quantity>0",
                    (interaction.user.id, interaction.guild.id, item_name)
                ) as c:
                    row = await c.fetchone()
                if not row:
                    return await interaction.response.send_message(embed=error_embed(
                        "Missing Item",
                        f"You don't have **{item_name}** in your inventory.\nCheck `/inventory`."
                    ))

            # Consume ingredients
            for item_name in [item1, item2]:
                await db.execute(
                    "UPDATE economy_inventory SET quantity=quantity-1 WHERE user_id=? AND guild_id=? AND LOWER(item_name)=LOWER(?)",
                    (interaction.user.id, interaction.guild.id, item_name)
                )
            # Add crafted item
            await db.execute(
                "INSERT INTO economy_inventory (user_id, guild_id, item_name, quantity) VALUES (?,?,?,1) ON CONFLICT(user_id,guild_id) DO UPDATE SET quantity=quantity+1",
                (interaction.user.id, interaction.guild.id, recipe["result_item"])
            )
            await db.commit()

        embed = success_embed(
            f"Crafted: {recipe['result_item']}!",
            f"Combined **{item1}** + **{item2}** → **{recipe['result_item']}**\n"
            + (f"**Bonus value:** +${recipe['result_value']:,}" if recipe.get("result_value") else "")
        )
        embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="craft-add", description="[Admin] Add a crafting recipe for this server.")
    @app_commands.describe(result="Item produced", ingredient1="First ingredient", ingredient2="Second ingredient", bonus_value="Bonus $ value added to wallet on craft")
    @app_commands.checks.has_permissions(administrator=True)
    async def craft_add(self, interaction: discord.Interaction, result: str, ingredient1: str, ingredient2: str, bonus_value: int = 0):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT INTO craft_recipes (guild_id, result_item, ingredient1, ingredient2, result_value) VALUES (?,?,?,?,?)",
                (interaction.guild.id, result, ingredient1, ingredient2, bonus_value)
            )
            await db.commit()
        await interaction.response.send_message(embed=success_embed(
            "Recipe Added",
            f"**{ingredient1}** + **{ingredient2}** → **{result}**"
            + (f"\n**Bonus value:** +${bonus_value:,}" if bonus_value else "")
        ))

    # ── /claim (community drop event) ─────────────────────────────────────
    @app_commands.command(name="claim", description="Claim a free reward during a Community Drop event!")
    async def claim(self, interaction: discord.Interaction):
        event = ACTIVE_EVENTS.get(interaction.guild.id)
        if not event or event.get("type") != "community_drop":
            return await interaction.response.send_message(embed=error_embed(
                "No Active Drop",
                "There's no Community Drop event active right now.\nEvents cycle automatically — check back soon!"
            ))
        # Give the reward
        reward = 2500
        await self.bot.db.update_economy(interaction.user.id, interaction.guild.id, wallet_delta=reward, earned_delta=reward)
        await interaction.response.send_message(embed=success_embed(
            "Community Drop Claimed!",
            f"You grabbed **${reward:,}** from the community drop!\n*This can only be claimed once per event.*"
        ))
        # Clear the event for this user (basic: just end the event globally after claim)
        ACTIVE_EVENTS.pop(interaction.guild.id, None)


# ── Heist Join View ────────────────────────────────────────────────────────────

class HeistJoinView(discord.ui.View):
    def __init__(self, bot, guild_id: int):
        super().__init__(timeout=60)
        self.bot      = bot
        self.guild_id = guild_id

    @discord.ui.button(label="🔫  Join Heist", style=discord.ButtonStyle.danger)
    async def join(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.guild_id not in ACTIVE_HEISTS:
            return await interaction.response.send_message("This heist is no longer active.")
        state = ACTIVE_HEISTS[self.guild_id]
        if interaction.user in state["participants"]:
            return await interaction.response.send_message("You're already in the crew!", ephemeral=True)
        data = await self.bot.db.get_economy(interaction.user.id, interaction.guild.id)
        if data["wallet"] < 200:
            return await interaction.response.send_message("You need **$200** in your wallet to join a heist.")
        state["participants"].append(interaction.user)
        new_pct = min(30 + (len(state["participants"]) - 1) * 8, 80)
        await interaction.response.send_message(
            f"🔫 You joined the crew! **{len(state['participants'])}** members. Success chance: **{new_pct}%**",
            ephemeral=True
        )

    @discord.ui.button(label="❌  Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.guild_id not in ACTIVE_HEISTS:
            return await interaction.response.send_message("No active heist.")
        state = ACTIVE_HEISTS[self.guild_id]
        if interaction.user.id != state["leader_id"]:
            return await interaction.response.send_message("Only the heist leader can cancel.")
        ACTIVE_HEISTS.pop(self.guild_id, None)
        await interaction.response.send_message(embed=info_embed("Heist Cancelled", "The heist has been called off."))


async def setup(bot):
    await bot.add_cog(EconomyAdvanced(bot))
