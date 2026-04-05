"""XERO Bot — /economy GroupCog"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, random, datetime, aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, economy_embed, XERO, FOOTER_ECO, comprehensive_embed

logger = logging.getLogger("XERO.Economy")
JOBS=[("Software Engineer",1400,2800),("Doctor",1600,3200),("Chef",700,1500),("Lawyer",1300,2600),("Artist",500,1200),("Pilot",1500,2900),("Teacher",800,1700),("Mechanic",750,1600),("Scientist",1100,2300),("Nurse",900,1900),("Writer",500,1100),("Trader",1200,2500),("Crypto Bro",200,5000),("Streamer",300,3000)]

class Economy(commands.GroupCog, name="economy"):
    def __init__(self, bot): self.bot = bot

    @app_commands.command(name="balance", description="Check wallet, bank, net worth, streak and server rank.")
    @app_commands.describe(user="User to check")
    async def balance(self, interaction: discord.Interaction, user: discord.Member = None):
        target=user or interaction.user
        data=await self.bot.db.get_economy(target.id,interaction.guild.id)
        streak=await self.bot.db.get_streak(target.id,interaction.guild.id)
        lb=await self.bot.db.get_economy_leaderboard(interaction.guild.id,200)
        rank=next((i+1 for i,r in enumerate(lb) if r["user_id"]==target.id),None)
        embed=economy_embed(target,data["wallet"],data["bank"],data["bank_limit"],streak.get("daily_streak",0),rank)
        embed.add_field(name="💼 Earned",value=f"${data.get('total_earned',0):,}",inline=True)
        embed.add_field(name="🛒 Spent",value=f"${data.get('total_spent',0):,}",inline=True)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="work", description="Work a job every hour to earn coins.")
    async def work(self, interaction: discord.Interaction):
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id)
        now=datetime.datetime.now()
        if data["last_work"]:
            rem=3600-(now-datetime.datetime.fromisoformat(data["last_work"])).total_seconds()
            if rem>0: return await interaction.response.send_message(embed=error_embed("Still Tired!",f"Rest **{int(rem//60)}m {int(rem%60)}s** first."),ephemeral=True)
        job,mn,mx=random.choice(JOBS); earned=random.randint(mn,mx)
        await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=earned,earned_delta=earned)
        await self.bot.db.set_economy_timestamp(interaction.user.id,interaction.guild.id,"last_work",now.isoformat())
        embed=success_embed("Work Complete!",f"Worked as **{job}** — earned **${earned:,}**!\n*Next work in 1 hour.*")
        embed.set_footer(text=FOOTER_ECO); await interaction.response.send_message(embed=embed)

    @app_commands.command(name="deposit", description="Move wallet→bank.")
    @app_commands.describe(amount="Amount or all")
    async def deposit(self, interaction: discord.Interaction, amount: str):
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id); space=data["bank_limit"]-data["bank"]
        amt=data["wallet"] if amount.lower()=="all" else (int(amount) if amount.isdigit() else -1)
        if amt<0: return await interaction.response.send_message(embed=error_embed("Invalid","Number or all."),ephemeral=True)
        amt=min(amt,space)
        if amt<=0 or amt>data["wallet"]: return await interaction.response.send_message(embed=error_embed("Can't Deposit",f"Wallet: ${data['wallet']:,} | Space: ${space:,}"),ephemeral=True)
        await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-amt,bank_delta=amt)
        await interaction.response.send_message(embed=success_embed("Deposited!",f"**${amt:,}** → bank. Bank: ${data['bank']+amt:,}/${data['bank_limit']:,}"))

    @app_commands.command(name="withdraw", description="Move bank→wallet.")
    @app_commands.describe(amount="Amount or all")
    async def withdraw(self, interaction: discord.Interaction, amount: str):
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id)
        amt=data["bank"] if amount.lower()=="all" else (int(amount) if amount.isdigit() else -1)
        if amt<0: return await interaction.response.send_message(embed=error_embed("Invalid","Number or all."),ephemeral=True)
        if amt<=0 or amt>data["bank"]: return await interaction.response.send_message(embed=error_embed("Insufficient",f"Bank: ${data['bank']:,}"),ephemeral=True)
        await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=amt,bank_delta=-amt)
        await interaction.response.send_message(embed=success_embed("Withdrawn!",f"**${amt:,}** → wallet."))

    @app_commands.command(name="pay", description="Send money to someone.")
    @app_commands.describe(user="Recipient",amount="Amount",note="Optional note")
    async def pay(self, interaction: discord.Interaction, user: discord.Member, amount: int, note: str=""):
        if user.bot or user==interaction.user: return await interaction.response.send_message(embed=error_embed("Invalid","Can't pay bots/yourself."),ephemeral=True)
        if amount<=0: return await interaction.response.send_message(embed=error_embed("Invalid","Positive only."),ephemeral=True)
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id)
        if amount>data["wallet"]: return await interaction.response.send_message(embed=error_embed("Not Enough",f"${data['wallet']:,}"),ephemeral=True)
        await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-amount,spent_delta=amount)
        await self.bot.db.update_economy(user.id,interaction.guild.id,wallet_delta=amount,earned_delta=amount)
        embed=success_embed("Sent!",f"{interaction.user.mention} → {user.mention}\n**${amount:,}**"+(f"\n*{note}*" if note else ""))
        embed.set_footer(text=FOOTER_ECO); await interaction.response.send_message(embed=embed)

    @app_commands.command(name="rob", description="Rob someone's wallet. 45% success, 1hr cooldown.")
    @app_commands.describe(user="Target")
    async def rob(self, interaction: discord.Interaction, user: discord.Member):
        if user.bot or user==interaction.user: return await interaction.response.send_message(embed=error_embed("Invalid","Can't rob bots/yourself."),ephemeral=True)
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id); now=datetime.datetime.now()
        if data["last_rob"]:
            rem=3600-(now-datetime.datetime.fromisoformat(data["last_rob"])).total_seconds()
            if rem>0: return await interaction.response.send_message(embed=error_embed("Lay Low!",f"Wait {int(rem//60)}m {int(rem%60)}s."),ephemeral=True)
        await self.bot.db.set_economy_timestamp(interaction.user.id,interaction.guild.id,"last_rob",now.isoformat())
        td=await self.bot.db.get_economy(user.id,interaction.guild.id)
        if td["wallet"]<100: return await interaction.response.send_message(embed=info_embed("Not Worth It",f"{user.display_name} only has ${td['wallet']:,}."))
        if random.random()<0.45:
            stolen=random.randint(int(td["wallet"]*0.1),int(td["wallet"]*0.4))
            await self.bot.db.update_economy(user.id,interaction.guild.id,wallet_delta=-stolen)
            await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=stolen,earned_delta=stolen)
            await interaction.response.send_message(embed=success_embed("Heist! 🎭",f"Swiped **${stolen:,}** from {user.mention}."))
        else:
            fine=min(random.randint(200,900),data["wallet"])
            await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-fine,spent_delta=fine)
            await interaction.response.send_message(embed=error_embed("Busted! 🚔",f"Paid **${fine:,}** in fines."))

    @app_commands.command(name="slots", description="Spin the slot machine.")
    @app_commands.describe(amount="Bet amount")
    async def slots(self, interaction: discord.Interaction, amount: int):
        if amount<=0: return await interaction.response.send_message(embed=error_embed("Invalid","Positive only."),ephemeral=True)
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id)
        if amount>data["wallet"]: return await interaction.response.send_message(embed=error_embed("Not Enough",f"${data['wallet']:,}"),ephemeral=True)
        SYMS=[("🍒",2),("🍋",2.5),("🍇",3),("🍀",4),("💎",8),("7️⃣",15),("🎰",20)]; W=[38,25,16,10,6,3,2]
        SL=[s[0] for s in SYMS]; M={s[0]:s[1] for s in SYMS}; s1,s2,s3=random.choices(SL,weights=W,k=3)
        if s1==s2==s3:
            mult=M[s1]; gain=int(amount*mult)-amount
            await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=gain,earned_delta=max(0,gain))
            color=XERO.GOLD; res=f"**JACKPOT!** ×{mult} — **${int(amount*mult):,}** 🎊"
        elif s1==s2 or s2==s3 or s1==s3:
            gain=int(amount*1.5)-amount
            await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=gain,earned_delta=max(0,gain))
            color=XERO.SUCCESS; res=f"Two of a kind! **${int(amount*1.5):,}**!"
        else:
            await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-amount,spent_delta=amount)
            color=XERO.ERROR; res=f"No match. Lost **${amount:,}**."
        # Personality comment
        won = s1==s2==s3 or s1==s2 or s2==s3 or s1==s3
        personality = self.bot.cogs.get("Personality")
        comment = await personality.get_slot_comment(won) if personality else ""
        embed=comprehensive_embed(title="🎰  Slot Machine",description=f"**[ {s1}  {s2}  {s3} ]**\n\n{res}" + (f"\n\n*{comment}*" if comment else ""),color=color)
        embed.set_footer(text=FOOTER_ECO); await interaction.response.send_message(embed=embed)

    @app_commands.command(name="blackjack", description="Play blackjack against the dealer.")
    @app_commands.describe(amount="Bet amount")
    async def blackjack(self, interaction: discord.Interaction, amount: int):
        if amount<=0: return await interaction.response.send_message(embed=error_embed("Invalid","Positive only."),ephemeral=True)
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id)
        if amount>data["wallet"]: return await interaction.response.send_message(embed=error_embed("Not Enough",f"${data['wallet']:,}"),ephemeral=True)
        deck=list(range(2,11))*4+["J","Q","K","A"]*4; random.shuffle(deck)
        def val(h):
            t,a=0,0
            for c in h:
                if c in("J","Q","K"):t+=10
                elif c=="A":t+=11;a+=1
                else:t+=c
            while t>21 and a:t-=10;a-=1
            return t
        def fmt(h): return " ".join(str(c) for c in h)
        p=[deck.pop(),deck.pop()]; d=[deck.pop(),deck.pop()]
        while val(d)<17: d.append(deck.pop())
        pv,dv=val(p),val(d)
        if pv>21: await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-amount,spent_delta=amount); res,color=f"Busted! ({pv}) Lost **${amount:,}**.",XERO.ERROR
        elif dv>21 or pv>dv: await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=amount,earned_delta=amount); res,color=f"You win! {pv} vs {dv}. **+${amount:,}**!",XERO.SUCCESS
        elif pv==dv: res,color=f"Push! {pv} vs {dv}.",XERO.WARNING
        else: await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-amount,spent_delta=amount); res,color=f"Dealer wins. {pv} vs {dv}. **-${amount:,}**.",XERO.ERROR
        embed=comprehensive_embed(title="🃏  Blackjack",color=color)
        embed.add_field(name=f"You ({pv})",value=fmt(p),inline=True); embed.add_field(name=f"Dealer ({dv})",value=fmt(d),inline=True)
        embed.add_field(name="Result",value=res,inline=False); embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="coinflip", description="Bet on heads or tails.")
    @app_commands.choices(side=[app_commands.Choice(name="Heads",value="heads"),app_commands.Choice(name="Tails",value="tails")])
    @app_commands.describe(side="Your call",amount="Bet amount")
    async def coinflip(self, interaction: discord.Interaction, side: str, amount: int):
        if amount<=0: return await interaction.response.send_message(embed=error_embed("Invalid","Positive only."),ephemeral=True)
        data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id)
        if amount>data["wallet"]: return await interaction.response.send_message(embed=error_embed("Not Enough",f"${data['wallet']:,}"),ephemeral=True)
        result=random.choice(["heads","tails"]); emoji="🟡" if result=="heads" else "⚫"
        if result==side:
            await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=amount,earned_delta=amount)
            embed=success_embed("You Won!",f"{emoji} **{result.capitalize()}** — **+${amount:,}**")
        else:
            await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-amount,spent_delta=amount)
            embed=error_embed("You Lost!",f"{emoji} **{result.capitalize()}** — **-${amount:,}**")
        embed.set_footer(text=FOOTER_ECO); await interaction.response.send_message(embed=embed)

    @app_commands.command(name="shop", description="Browse the server shop.")
    async def shop(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory=aiosqlite.Row
            async with db.execute("SELECT * FROM economy_shop WHERE guild_id=? ORDER BY price ASC",(interaction.guild.id,)) as c:
                items=[dict(r) for r in await c.fetchall()]
        if not items: return await interaction.response.send_message(embed=info_embed("Shop Empty","No items yet. Admins: `/economy shop-add`."))
        embed=comprehensive_embed(title=f"🛒  {interaction.guild.name} Shop",description="Use `/economy buy <item>` to purchase.",color=XERO.GOLD)
        for item in items[:20]:
            stock="∞" if item["stock"]<0 else str(item["stock"])
            embed.add_field(name=f"{item['emoji']} {item['name']}  •  ${item['price']:,}",value=f"{item['description']}\n*Stock: {stock}*",inline=True)
        embed.set_footer(text=FOOTER_ECO); await interaction.response.send_message(embed=embed)

    @app_commands.command(name="shop-add", description="[Admin] Add an item to the shop.")
    @app_commands.describe(name="Item name",price="Price",description="Description",role="Role to grant",emoji="Emoji",stock="Stock (-1=unlimited)")
    @app_commands.checks.has_permissions(administrator=True)
    async def shop_add(self, interaction: discord.Interaction, name: str, price: int, description: str="A shop item.", role: discord.Role=None, emoji: str="🛍️", stock: int=-1):
        async with self.bot.db._db_context() as db:
            await db.execute("INSERT INTO economy_shop (guild_id,name,description,price,role_id,emoji,stock) VALUES (?,?,?,?,?,?,?)",(interaction.guild.id,name,description,max(0,price),role.id if role else None,emoji,stock)); await db.commit()
        await interaction.response.send_message(embed=success_embed("Item Added!",f"**{emoji} {name}** — ${price:,}"))

    @app_commands.command(name="shop-remove", description="[Admin] Remove an item.")
    @app_commands.checks.has_permissions(administrator=True)
    async def shop_remove(self, interaction: discord.Interaction, name: str):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM economy_shop WHERE guild_id=? AND LOWER(name)=LOWER(?)",(interaction.guild.id,name)); await db.commit()
        await interaction.response.send_message(embed=success_embed("Removed",f"**{name}** removed."))

    @app_commands.command(name="buy", description="Purchase an item from the shop.")
    @app_commands.describe(item_name="Item to buy")
    async def buy(self, interaction: discord.Interaction, item_name: str):
        async with self.bot.db._db_context() as db:
            db.row_factory=aiosqlite.Row
            async with db.execute("SELECT * FROM economy_shop WHERE guild_id=? AND LOWER(name)=LOWER(?)",(interaction.guild.id,item_name)) as c: item=await c.fetchone()
        if not item: return await interaction.response.send_message(embed=error_embed("Not Found",f"No `{item_name}`. Check `/economy shop`."),ephemeral=True)
        item=dict(item); data=await self.bot.db.get_economy(interaction.user.id,interaction.guild.id)
        if data["wallet"]<item["price"]: return await interaction.response.send_message(embed=error_embed("Not Enough",f"Costs **${item['price']:,}**, have **${data['wallet']:,}**."),ephemeral=True)
        if item["stock"]==0: return await interaction.response.send_message(embed=error_embed("Out of Stock","Sold out!"),ephemeral=True)
        await self.bot.db.update_economy(interaction.user.id,interaction.guild.id,wallet_delta=-item["price"],spent_delta=item["price"])
        async with self.bot.db._db_context() as db:
            try: await db.execute("INSERT INTO economy_inventory (user_id,guild_id,item_name,quantity) VALUES (?,?,?,1)",(interaction.user.id,interaction.guild.id,item["name"]))
            except: await db.execute("UPDATE economy_inventory SET quantity=quantity+1 WHERE user_id=? AND guild_id=? AND item_name=?",(interaction.user.id,interaction.guild.id,item["name"]))
            if item["stock"]>0: await db.execute("UPDATE economy_shop SET stock=stock-1 WHERE item_id=?",(item["item_id"],))
            await db.commit()
        if item.get("role_id"):
            role=interaction.guild.get_role(item["role_id"])
            if role:
                try: await interaction.user.add_roles(role)
                except: pass
        await interaction.response.send_message(embed=success_embed("Purchased!",f"**{item['emoji']} {item['name']}** — **${item['price']:,}**!"))

    @app_commands.command(name="inventory", description="View your shop inventory.")
    @app_commands.describe(user="User to check")
    async def inventory(self, interaction: discord.Interaction, user: discord.Member=None):
        target=user or interaction.user
        async with self.bot.db._db_context() as db:
            db.row_factory=aiosqlite.Row
            async with db.execute("SELECT item_name,SUM(quantity) as qty FROM economy_inventory WHERE user_id=? AND guild_id=? GROUP BY item_name ORDER BY qty DESC",(target.id,interaction.guild.id)) as c:
                items=[dict(r) for r in await c.fetchall()]
        if not items: return await interaction.response.send_message(embed=info_embed("Empty","No items."))
        embed=comprehensive_embed(title=f"🎒  {target.display_name}'s Inventory",description=f"**{len(items)}** item type(s)",color=XERO.GOLD,thumbnail_url=target.display_avatar.url)
        for item in items[:20]: embed.add_field(name=item["item_name"],value=f"× {item['qty']}",inline=True)
        embed.set_footer(text=FOOTER_ECO); await interaction.response.send_message(embed=embed)

    @app_commands.command(name="rich", description="Server wealth leaderboard.")
    async def rich(self, interaction: discord.Interaction):
        lb=await self.bot.db.get_economy_leaderboard(interaction.guild.id,10)
        if not lb: return await interaction.response.send_message(embed=info_embed("No Data","No economy data yet."))
        medals=["🥇","🥈","🥉"]+[f"**#{i}**" for i in range(4,11)]
        embed=comprehensive_embed(title="💰  Richest Members",description="",color=XERO.GOLD)
        desc=""
        for i,row in enumerate(lb):
            u=interaction.guild.get_member(row["user_id"]); n=u.display_name if u else f"User {row['user_id']}"
            desc+=f"{medals[i]} **{n}** — ${row['total']:,}\n"
        embed.description=desc; embed.set_footer(text=FOOTER_ECO)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="give", description="[Admin] Give or remove money.")
    @app_commands.describe(user="Target",amount="Amount",to_bank="To bank instead")
    @app_commands.checks.has_permissions(administrator=True)
    async def give(self, interaction: discord.Interaction, user: discord.Member, amount: int, to_bank: bool=False):
        if to_bank: await self.bot.db.update_economy(user.id,interaction.guild.id,bank_delta=amount)
        else: await self.bot.db.update_economy(user.id,interaction.guild.id,wallet_delta=amount)
        act="Added" if amount>=0 else "Removed"; loc="bank" if to_bank else "wallet"
        await interaction.response.send_message(embed=success_embed("Done",f"{act} **${abs(amount):,}** from {user.mention}'s {loc}."),ephemeral=True)

    @app_commands.command(name="reset-user", description="[Admin] Wipe a user's economy data.")
    @app_commands.checks.has_permissions(administrator=True)
    async def reset_user(self, interaction: discord.Interaction, user: discord.Member):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM economy WHERE user_id=? AND guild_id=?",(user.id,interaction.guild.id)); await db.commit()
        await interaction.response.send_message(embed=success_embed("Reset",f"{user.mention}'s economy wiped."),ephemeral=True)

async def setup(bot):
    await bot.add_cog(Economy(bot))
