"""XERO Bot — Core Utility (ping, remind, poll, afk, help) — tools moved to /tools"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, time, datetime
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed, XERO

logger = logging.getLogger("XERO.Utility")

class Paginator(discord.ui.View):
    def __init__(self, items, title, user_id, items_per_page=10):
        super().__init__(timeout=60)
        self.items = items
        self.title = title
        self.user_id = user_id
        self.items_per_page = items_per_page
        self.current_page = 0
        self.total_pages = (len(items) - 1) // items_per_page + 1

    def create_embed(self):
        start = self.current_page * self.items_per_page
        end = start + self.items_per_page
        current_items = self.items[start:end]
        
        desc = "\n".join(current_items)
        embed = info_embed(
            f"{self.title} (Page {self.current_page + 1}/{self.total_pages})",
            desc
        )
        embed.set_footer(text=f"Total: {len(self.items)} items")
        return embed

    @discord.ui.button(label="<", style=discord.ButtonStyle.primary)
    async def prev_page(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            return await interaction.response.send_message("This menu is not for you.", ephemeral=True)
        
        if self.current_page > 0:
            self.current_page -= 1
            await interaction.response.edit_message(embed=self.create_embed(), view=self)
        else:
            await interaction.response.defer()

    @discord.ui.button(label=">", style=discord.ButtonStyle.primary)
    async def next_page(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            return await interaction.response.send_message("This menu is not for you.", ephemeral=True)
        
        if self.current_page < self.total_pages - 1:
            self.current_page += 1
            await interaction.response.edit_message(embed=self.create_embed(), view=self)
        else:
            await interaction.response.defer()

class Utility(commands.Cog):
    def __init__(self, bot): self.bot = bot

    @app_commands.command(name="ping", description="Check bot latency, memory, CPU, uptime, and server count.")
    async def ping(self, interaction: discord.Interaction):
        latency=round(self.bot.latency*1000); uptime=time.time()-self.bot.launch_time
        up_str=f"{int(uptime//86400)}d {int((uptime%86400)//3600)}h {int((uptime%3600)//60)}m"
        try:
            import psutil, os; proc=psutil.Process(os.getpid()); mem=proc.memory_info().rss/1024/1024; cpu=proc.cpu_percent(interval=0.1)
        except: mem,cpu=0.0,0.0
        rating="🟢" if latency<80 else "🟡" if latency<150 else "🔴"
        embed=comprehensive_embed(title="🏓 XERO Performance",color=XERO.PRIMARY)
        embed.add_field(name="⚡ Latency",value=f"**{latency}ms** {rating}",inline=True)
        embed.add_field(name="💾 Memory",value=f"**{mem:.1f} MB**",inline=True)
        embed.add_field(name="🖥️ CPU",value=f"**{cpu:.1f}%**",inline=True)
        embed.add_field(name="⏱️ Uptime",value=f"**{up_str}**",inline=True)
        embed.add_field(name="🌐 Servers",value=f"**{len(self.bot.guilds):,}**",inline=True)
        embed.add_field(name="👥 Users",value=f"**{sum(g.member_count for g in self.bot.guilds):,}**",inline=True)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="remind", description="Set a reminder — bot pings you in this channel when time is up.")
    @app_commands.describe(message="What to remind you about",minutes="Minutes from now (max 10080 = 7 days)")
    async def remind(self, interaction: discord.Interaction, message: str, minutes: int=10):
        minutes=max(1,min(10080,minutes))
        remind_at=(datetime.datetime.now(datetime.timezone.utc)+datetime.timedelta(minutes=minutes)).strftime("%Y-%m-%d %H:%M:%S")
        rid=await self.bot.db.add_reminder(interaction.user.id,interaction.channel.id,message,remind_at)
        ts=int((datetime.datetime.now(datetime.timezone.utc)+datetime.timedelta(minutes=minutes)).timestamp())
        hrs,mins_=minutes//60,minutes%60; time_str=f"{hrs}h {mins_}m" if hrs else f"{mins_}m"
        await interaction.response.send_message(embed=success_embed("⏰ Reminder Set!",f"I'll remind you in **{time_str}** (<t:{ts}:R>)\n**Message:** {message}\n**ID:** #{rid}"),ephemeral=True)

    @app_commands.command(name="poll", description="Create an interactive poll with up to 4 options and auto-reactions.")
    @app_commands.describe(question="Poll question",option1="Option 1",option2="Option 2",option3="Option 3",option4="Option 4")
    async def poll(self, interaction: discord.Interaction, question: str, option1: str, option2: str, option3: str=None, option4: str=None):
        options=[o for o in [option1,option2,option3,option4] if o]; emojis=["1️⃣","2️⃣","3️⃣","4️⃣"]
        embed=comprehensive_embed(title=f"📊 {question}",color=XERO.PRIMARY)
        for i,opt in enumerate(options): embed.add_field(name=f"{emojis[i]} Option {i+1}",value=opt,inline=False)
        embed.set_footer(text=f"Poll by {interaction.user.display_name} • React to vote!")
        msg=await interaction.channel.send(embed=embed)
        for i in range(len(options)): await msg.add_reaction(emojis[i])
        await interaction.response.send_message(embed=success_embed("Poll Created!",f"Your poll is live with **{len(options)}** options."),ephemeral=True)

    @app_commands.command(name="afk", description="Set yourself AFK — XERO notifies anyone who pings you.")
    @app_commands.describe(reason="Why you're going AFK")
    async def afk(self, interaction: discord.Interaction, reason: str="AFK"):
        await self.bot.db.set_afk(interaction.user.id,interaction.guild.id,reason[:200])
        await interaction.response.send_message(embed=info_embed("💤 AFK Set",f"You're now AFK: **{reason}**\nI'll notify anyone who pings you. Automatically cleared when you send a message."))

    @app_commands.command(name="invite", description="Get the invite link for XERO Bot.")
    async def invite(self, interaction: discord.Interaction):
        url = discord.utils.oauth_url(self.bot.user.id, permissions=discord.Permissions(8), scopes=("bot", "applications.commands"))
        embed = comprehensive_embed(title="👋 Invite XERO", description="Click below to add XERO to your server!\n• 400+ Commands\n• AI & Music\n• 100% Free", color=XERO.PRIMARY)
        view = discord.ui.View().add_item(discord.ui.Button(label="Invite XERO", url=url, style=discord.ButtonStyle.link))
        await interaction.response.send_message(embed=embed, view=view)

    @app_commands.command(name="commands", description="Browse all 400+ XERO commands organized by category.")
    async def help(self, interaction: discord.Interaction):
        # Dynamically calculate total commands
        total_cmds = 0
        for cog_name, cog in self.bot.cogs.items():
            for cmd in cog.get_app_commands():
                total_cmds += 1
                if isinstance(cmd, app_commands.Group):
                    total_cmds += len(cmd.commands)
        
        embed=comprehensive_embed(
            title="📚 XERO — Complete Command Reference",
            description=f"**{total_cmds}** commands found. Premium features, completely free.\n**Use `/info bot` for bot stats.**",
            color=XERO.PRIMARY,
            thumbnail_url=self.bot.user.display_avatar.url
        )
        
        cats=[
            ("⚙️ Config","`/config` · `/settings` · `/branding` · `/view`"),
            ("ℹ️ Info","user · server · role · channel · bot · emoji · invite · permissions"),
            ("🛡️ Moderation","warn · warnings · clearwarns · kick · ban · unban · softban · timeout · untimeout · purge · slowmode · lock · unlock · nick · history"),
            ("🤖 AI","ask · chat · summarize · translate · brainstorm · code-explain · code-debug · sentiment · rewrite · grammar · generate · fact-check · roast · analyze-image · clear-memory"),
            ("🧪 Nexus","debate · rpg-start · rpg-action · rpg-quit · mod-advice · coach · explain"),
            ("💰 Economy","balance · work · daily · streak · heist · deposit · withdraw · pay · rob · slots · blackjack · coinflip · shop · buy · inventory · rich · give"),
            ("📈 Stocks","stocks · buy-stock · sell-stock · portfolio · event"),
            ("📊 Levels","rank · leaderboard · set-xp · add-xp · reset · reward-add · reward-remove · rewards"),
            ("📈 Analytics","overview · top-members · economy-stats · moderation-stats · level-stats · member-growth · channel-activity"),
            ("🎮 Fun","8ball · roll · choose · ship · meme · fact · cat · dog · rps · trivia · joke · would-you-rather · never-have-i-ever · fortune · rate"),
            ("🎭 Social","hug · kiss · pat · slap · cuddle · dance · highfive · wave · bite · poke · stare · shoot"),
            ("🎉 Giveaway","start · end · reroll · list · cancel · edit-prize · winners · delete"),
            ("📢 Announcement","send · schedule · list · cancel · edit · mention-role · set-channel"),
            ("🛡️ Aegis","`/verify setup` (4-Tier Protection)"),
            ("🎫 Ticket","setup · create · close · add · remove · list · transcript"),
            ("🎵 Music","play · pause · resume · skip · stop · queue · nowplaying · volume · loop · remove · shuffle · clear"),
            ("🎭 Roles","add · remove · info · members · create · delete · color · rename · all · give-all · take-all · bots"),
            ("🏰 Server","icon · banner · bans · invites · create-invite · channels · members · boosts · audit-log · lockdown · unlockdown · nuke"),
            ("🧠 Smart Mod","health · raid-config · escalation-config · raid-log · lockdown · unlockdown · warn-stats"),
            ("🎂 Birthday","set · remove · view · list · setup-channel · announce · today"),
            ("💡 Suggest","submit · approve · deny · implement · consider · list · setup"),
            ("📌 Reaction Roles","create-panel · add-role · publish · list-panels · delete-panel"),
            ("⭐ Starboard","setup · toggle · threshold · config"),
            ("🔢 Counting","setup · stats · reset · toggle · leaderboard"),
            ("🤫 Confess","send · setup · reveal · delete"),
            ("📋 Custom Commands","create · use · list · edit · delete · info"),
            ("🔊 Temp Voice","setup · rename · limit · lock · unlock · active"),
            ("🎨 Profile","card · achievements · compare · generate · variations · avatar-style"),
            ("🔧 Tools","calc · timestamp · weather · define · color · emojis · snipe"),
            ("🔑 Core","/ping · /remind · /poll · /afk · /help · /admin · /purge-bots"),
            ("🛠️ Utility","/roles · /channels"),
        ]
        
        for name, cmds in cats:
            embed.add_field(name=name, value=cmds, inline=True)
            
        embed.set_footer(text="XERO Bot by Team Flame • Built to dust every other bot.")
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="reminders", description="View and manage all your active reminders.")
    async def reminders(self, interaction: discord.Interaction):
        import aiosqlite
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT id, message, remind_at, channel_id FROM reminders WHERE user_id=? AND sent=0 ORDER BY remind_at",
                (interaction.user.id,)
            ) as c:
                rows = [dict(r) for r in await c.fetchall()]
        if not rows:
            return await interaction.response.send_message(embed=info_embed("No Reminders","You have no active reminders. Use `/remind` to create one."))
        embed = comprehensive_embed(title=f"⏰  Your Reminders ({len(rows)})", color=0x00D4FF)
        for r in rows:
            try:
                dt  = datetime.datetime.fromisoformat(r["remind_at"])
                ts  = int(dt.replace(tzinfo=datetime.timezone.utc).timestamp())
                ch  = interaction.guild.get_channel(r["channel_id"]) if interaction.guild else None
                ch_str = ch.mention if ch else "DM"
                embed.add_field(
                    name=f"📌 Reminder #{r['id']}",
                    value=f"**Message:** {r['message'][:100]}\n**When:** <t:{ts}:R>\n**Channel:** {ch_str}",
                    inline=False
                )
            except Exception: pass
        embed.set_footer(text="Use /cancel-reminder <id> to cancel one")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="cancel-reminder", description="Cancel an active reminder by its ID.")
    @app_commands.describe(reminder_id="Reminder ID (from /reminders)")
    async def cancel_reminder(self, interaction: discord.Interaction, reminder_id: int):
        import aiosqlite
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT user_id FROM reminders WHERE id=?", (reminder_id,)) as c:
                row = await c.fetchone()
            if not row:
                return await interaction.response.send_message(embed=error_embed("Not Found", f"Reminder #{reminder_id} not found."), ephemeral=True)
            if row[0] != interaction.user.id:
                return await interaction.response.send_message(embed=error_embed("Not Yours", "You can only cancel your own reminders."), ephemeral=True)
            await db.execute("UPDATE reminders SET sent=1 WHERE id=?", (reminder_id,))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Reminder Cancelled", f"Reminder #{reminder_id} has been cancelled."))

    @app_commands.command(name="snipe", description="See the last deleted message in this channel.")
    async def snipe(self, interaction: discord.Interaction):
        snipes = getattr(self.bot, '_snipe_cache', {})
        msg = snipes.get(interaction.channel.id)
        if not msg:
            return await interaction.response.send_message(embed=info_embed("Nothing to Snipe","No recently deleted messages cached."))
        embed = comprehensive_embed(description=msg['content'] or "*no text*", color=0xFF3B5C, timestamp=msg['deleted_at'])
        embed.set_author(name=msg['author'], icon_url=msg['avatar'])
        embed.set_footer(text=f"Sniped from #{interaction.channel.name}  •  XERO Snipe")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="roles", description="List all roles in the server with their IDs and member counts.")
    async def list_roles(self, interaction: discord.Interaction):
        roles = sorted(interaction.guild.roles, key=lambda r: r.position, reverse=True)
        items = []
        for r in roles:
            items.append(f"▹ **{r.name}**\n  ID: `{r.id}` | Members: `{len(r.members)}`")
        
        view = Paginator(items, f"Roles in {interaction.guild.name}", interaction.user.id)
        await interaction.response.send_message(embed=view.create_embed(), view=view)

    @app_commands.command(name="channels", description="List all channels in the server with their IDs.")
    async def list_channels(self, interaction: discord.Interaction):
        channels = sorted(interaction.guild.channels, key=lambda c: (str(c.type), c.position))
        items = []
        for c in channels:
            type_icon = "💬" if isinstance(c, discord.TextChannel) else "🔊" if isinstance(c, discord.VoiceChannel) else "📁" if isinstance(c, discord.CategoryChannel) else "📝"
            items.append(f"{type_icon} **{c.name}**\n  ID: `{c.id}` | Type: `{str(c.type).replace('Channel', '')}`")
        
        view = Paginator(items, f"Channels in {interaction.guild.name}", interaction.user.id)
        await interaction.response.send_message(embed=view.create_embed(), view=view)

async def setup(bot):
    await bot.add_cog(Utility(bot))
