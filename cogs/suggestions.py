"""XERO Bot — Suggestions with live voting buttons"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed, XERO, FOOTER_MAIN

logger = logging.getLogger("XERO.Suggestions")
STATUS_COLORS={"pending":XERO.PRIMARY,"approved":XERO.SUCCESS,"denied":XERO.ERROR,"implemented":XERO.GOLD,"considering":XERO.WARNING}
STATUS_EMOJIS={"pending":"🔵","approved":"✅","denied":"❌","implemented":"🚀","considering":"🤔"}

def sug_embed(sid,title,desc,author,avatar,status,up,down,note=None):
    color=STATUS_COLORS.get(status,XERO.PRIMARY); total=up+down; pct=int(up/total*100) if total else 50
    bar="█"*int(pct/5)+"░"*(20-int(pct/5))
    embed=comprehensive_embed(title=f"💡  #{sid}  •  {title}",description=desc,color=color)
    embed.set_author(name=f"Suggested by {author}",icon_url=avatar or discord.Embed.Empty)
    embed.add_field(name="Status",value=f"{STATUS_EMOJIS.get(status,'🔵')} **{status.capitalize()}**",inline=True)
    embed.add_field(name="👍 Up",value=str(up),inline=True); embed.add_field(name="👎 Down",value=str(down),inline=True)
    embed.add_field(name=f"Approval ({pct}%)",value=f"`{bar}`",inline=False)
    if note: embed.add_field(name="📋 Staff Note",value=note,inline=False)
    embed.set_footer(text="Vote with the buttons!"); return embed

class VoteView(discord.ui.View):
    def __init__(self,bot,sid):
        super().__init__(timeout=None); self.bot=bot; self.sid=sid
    @discord.ui.button(emoji="👍",label="Upvote",style=discord.ButtonStyle.success,custom_id="sug_up")
    async def upvote(self,interaction,button): await self._vote(interaction,"up")
    @discord.ui.button(emoji="👎",label="Downvote",style=discord.ButtonStyle.danger,custom_id="sug_down")
    async def downvote(self,interaction,button): await self._vote(interaction,"down")
    async def _vote(self,interaction,vtype):
        async with self.bot.db._db_context() as db:
            db.row_factory=aiosqlite.Row
            async with db.execute("SELECT vote FROM suggestion_votes WHERE suggestion_id=? AND user_id=?",(self.sid,interaction.user.id)) as c: existing=await c.fetchone()
            if existing:
                if existing["vote"]==vtype:
                    await db.execute("DELETE FROM suggestion_votes WHERE suggestion_id=? AND user_id=?",(self.sid,interaction.user.id))
                    col="upvotes" if vtype=="up" else "downvotes"
                    await db.execute(f"UPDATE suggestions SET {col}={col}-1 WHERE id=?",(self.sid,)); await db.commit()
                    return await interaction.response.send_message("Vote removed.",ephemeral=True)
                else:
                    old="upvotes" if existing["vote"]=="up" else "downvotes"; new="upvotes" if vtype=="up" else "downvotes"
                    await db.execute("UPDATE suggestion_votes SET vote=? WHERE suggestion_id=? AND user_id=?",(vtype,self.sid,interaction.user.id))
                    await db.execute(f"UPDATE suggestions SET {old}={old}-1,{new}={new}+1 WHERE id=?",(self.sid,))
            else:
                await db.execute("INSERT INTO suggestion_votes (suggestion_id,user_id,vote) VALUES (?,?,?)",(self.sid,interaction.user.id,vtype))
                col="upvotes" if vtype=="up" else "downvotes"
                await db.execute(f"UPDATE suggestions SET {col}={col}+1 WHERE id=?",(self.sid,))
            await db.commit()
            async with db.execute("SELECT * FROM suggestions WHERE id=?",(self.sid,)) as c: s=await c.fetchone()
        if not s: return await interaction.response.send_message("Not found.",ephemeral=True)
        s=dict(s)
        embed=sug_embed(s["id"],s.get("title","Suggestion"),s["description"],s.get("author_name","Unknown"),s.get("author_avatar"),s["status"],s.get("upvotes",0),s.get("downvotes",0),s.get("staff_response"))
        await interaction.response.edit_message(embed=embed,view=self)

class Suggestions(commands.GroupCog, name="suggest"):
    def __init__(self,bot): self.bot=bot

    async def _ensure(self):
        async with self.bot.db._db_context() as db:
            await db.execute("CREATE TABLE IF NOT EXISTS suggestion_votes (suggestion_id INTEGER NOT NULL,user_id INTEGER NOT NULL,vote TEXT NOT NULL,PRIMARY KEY(suggestion_id,user_id))")
            for col in ["upvotes INTEGER DEFAULT 0","downvotes INTEGER DEFAULT 0","title TEXT DEFAULT 'Suggestion'","author_name TEXT","author_avatar TEXT"]:
                try: await db.execute(f"ALTER TABLE suggestions ADD COLUMN {col}")
                except: pass
            try: await db.execute("ALTER TABLE guild_settings ADD COLUMN suggestion_channel_id INTEGER")
            except: pass
            await db.commit()

    @app_commands.command(name="submit",description="Submit a suggestion with live voting.")
    @app_commands.describe(title="Short title",description="Full details")
    async def submit(self,interaction:discord.Interaction,title:str,description:str):
        await self._ensure()
        settings=await self.bot.db.get_guild_settings(interaction.guild.id); channel_id=settings.get("suggestion_channel_id")
        if not channel_id: return await interaction.response.send_message(embed=error_embed("Not Configured","Admins: run `/suggest setup` first."),ephemeral=True)
        channel=interaction.guild.get_channel(channel_id)
        if not channel: return await interaction.response.send_message(embed=error_embed("Bad Channel","Suggestion channel missing. Contact an admin."),ephemeral=True)
        async with self.bot.db._db_context() as db:
            async with db.execute("INSERT INTO suggestions (guild_id,user_id,channel_id,title,description,author_name,author_avatar) VALUES (?,?,?,?,?,?,?)",(interaction.guild.id,interaction.user.id,channel_id,title[:100],description[:1000],interaction.user.display_name,str(interaction.user.display_avatar.url))) as c: sid=c.lastrowid
            await db.commit()
        from utils.embeds import brand_embed, comprehensive_embed
        embed=sug_embed(sid,title,description,interaction.user.display_name,str(interaction.user.display_avatar.url),"pending",0,0)
        
        # Unified Branding
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        view=VoteView(self.bot,sid)
        if file:
            msg=await channel.send(embed=embed,view=view,file=file)
        else:
            msg=await channel.send(embed=embed,view=view)
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE suggestions SET message_id=? WHERE id=?",(msg.id,sid)); await db.commit()
        await interaction.response.send_message(embed=success_embed("Submitted!",f"Suggestion **#{sid}** posted in {channel.mention} for voting!"),ephemeral=True)

    async def _set_status(self,interaction,sid,status,note=None):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            db.row_factory=aiosqlite.Row
            async with db.execute("SELECT * FROM suggestions WHERE id=? AND guild_id=?",(sid,interaction.guild.id)) as c: s=await c.fetchone()
        if not s: return await interaction.response.send_message(embed=error_embed("Not Found",f"Suggestion #{sid} not found."),ephemeral=True)
        s=dict(s)
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE suggestions SET status=?,staff_response=?,reviewed_by=? WHERE id=?",(status,note,interaction.user.id,sid)); await db.commit()
        channel=interaction.guild.get_channel(s["channel_id"])
        if channel and s.get("message_id"):
            try:
                msg=await channel.fetch_message(s["message_id"])
                async with self.bot.db._db_context() as db:
                    db.row_factory=aiosqlite.Row
                    async with db.execute("SELECT * FROM suggestions WHERE id=?",(sid,)) as c: upd=dict(await c.fetchone())
                embed=sug_embed(sid,upd.get("title","Suggestion"),upd["description"],upd.get("author_name","Unknown"),upd.get("author_avatar"),status,upd.get("upvotes",0),upd.get("downvotes",0),note)
                await msg.edit(embed=embed,view=VoteView(self.bot,sid))
            except Exception as e: logger.error(f"Suggestion update: {e}")
        await interaction.response.send_message(embed=success_embed(f"Suggestion {status.capitalize()}",f"#{sid} marked **{status}**."+(f"\nNote: {note}" if note else "")))

    @app_commands.command(name="approve",description="[Staff] Approve a suggestion.")
    @app_commands.describe(id="Suggestion ID",note="Optional staff note")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def approve(self,i:discord.Interaction,id:int,note:str=None): await self._set_status(i,id,"approved",note)

    @app_commands.command(name="deny",description="[Staff] Deny a suggestion.")
    @app_commands.describe(id="Suggestion ID",reason="Reason")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def deny(self,i:discord.Interaction,id:int,reason:str=None): await self._set_status(i,id,"denied",reason)

    @app_commands.command(name="implement",description="[Staff] Mark as implemented.")
    @app_commands.describe(id="Suggestion ID",note="Note")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def implement(self,i:discord.Interaction,id:int,note:str=None): await self._set_status(i,id,"implemented",note)

    @app_commands.command(name="consider",description="[Staff] Mark as under consideration.")
    @app_commands.describe(id="Suggestion ID",note="Note")
    @app_commands.checks.has_permissions(manage_messages=True)
    async def consider(self,i:discord.Interaction,id:int,note:str=None): await self._set_status(i,id,"considering",note)

    @app_commands.command(name="list",description="Browse all suggestions with live vote counts.")
    @app_commands.choices(status=[app_commands.Choice(name=s.capitalize(),value=s) for s in ["all","pending","approved","denied","implemented","considering"]])
    @app_commands.describe(status="Filter by status")
    async def list(self,interaction:discord.Interaction,status:str="all"):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            db.row_factory=aiosqlite.Row
            if status=="all":
                async with db.execute("SELECT * FROM suggestions WHERE guild_id=? ORDER BY id DESC LIMIT 15",(interaction.guild.id,)) as c: rows=[dict(r) for r in await c.fetchall()]
            else:
                async with db.execute("SELECT * FROM suggestions WHERE guild_id=? AND status=? ORDER BY id DESC LIMIT 15",(interaction.guild.id,status)) as c: rows=[dict(r) for r in await c.fetchall()]
        if not rows: return await interaction.response.send_message(embed=info_embed("No Suggestions","Nothing found."))
        embed=comprehensive_embed(title=f"💡  Suggestions — {status.capitalize()}",description=f"**{len(rows)}** result(s)",color=XERO.PRIMARY)
        for s in rows:
            emoji=STATUS_EMOJIS.get(s["status"],"🔵")
            embed.add_field(name=f"#{s['id']}  {emoji}  {s.get('title','Suggestion')[:40]}",value=f"👍 {s.get('upvotes',0)} · 👎 {s.get('downvotes',0)} · {s.get('author_name','Unknown')}",inline=False)
        embed.set_footer(text=FOOTER_MAIN); await interaction.response.send_message(embed=embed)

    @app_commands.command(name="setup",description="[Admin] Set the suggestions channel.")
    @app_commands.describe(channel="Channel for suggestions")
    @app_commands.checks.has_permissions(administrator=True)
    async def setup(self,interaction:discord.Interaction,channel:discord.TextChannel):
        await self._ensure()
        async with self.bot.db._db_context() as db:
            await db.execute("INSERT OR IGNORE INTO guild_settings (guild_id) VALUES (?)",(interaction.guild.id,))
            await db.execute("UPDATE guild_settings SET suggestion_channel_id=? WHERE guild_id=?",(channel.id,interaction.guild.id)); await db.commit()
        await interaction.response.send_message(embed=success_embed("Configured!",f"Suggestions → {channel.mention} with live voting."))

async def setup(bot):
    await bot.add_cog(Suggestions(bot))
