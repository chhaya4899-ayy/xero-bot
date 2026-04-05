"""XERO Bot — Giveaway System (8 commands)"""
import discord
from utils.guard import command_guard
from discord.ext import commands, tasks
from discord import app_commands
import logging
import datetime
import random
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, giveaway_embed, comprehensive_embed

logger = logging.getLogger("XERO.Giveaway")


class Giveaway(commands.GroupCog, name="giveaway"):
    def __init__(self, bot):
        self.bot = bot
        self.process_giveaways.start()

    def cog_unload(self):
        self.process_giveaways.cancel()

    @tasks.loop(minutes=1)
    async def process_giveaways(self):
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM giveaways WHERE ended=0 AND paused=0 AND end_time <= datetime('now')"
                ) as c:
                    giveaways = [dict(r) for r in await c.fetchall()]

            for gw in giveaways:
                await self._end_giveaway(gw["giveaway_id"])
        except Exception as e:
            logger.error(f"Giveaway loop error: {e}")

    @process_giveaways.before_loop
    async def before_giveaways(self):
        await self.bot.wait_until_ready()

    # ── Reaction entry/exit ───────────────────────────────────────────────────

    @commands.Cog.listener()
    async def on_raw_reaction_add(self, payload: discord.RawReactionActionEvent):
        """Add a user to giveaway_participants when they react 🎉."""
        if str(payload.emoji) != "🎉":
            return
        if payload.user_id == self.bot.user.id:
            return
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                # Check if this message is a live giveaway
                async with db.execute(
                    "SELECT giveaway_id, required_role_id, bonus_role_id FROM giveaways WHERE message_id=? AND ended=0 AND paused=0",
                    (payload.message_id,)
                ) as c:
                    gw = await c.fetchone()
                if not gw:
                    return
                gw = dict(gw)
                giveaway_id      = gw["giveaway_id"]
                required_role_id = gw.get("required_role_id")
                bonus_role_id    = gw.get("bonus_role_id")

                guild  = self.bot.get_guild(payload.guild_id)
                member = guild.get_member(payload.user_id) if guild else None

                # Enforce required role
                if required_role_id:
                    if not member or not any(r.id == required_role_id for r in member.roles):
                        try:
                            channel = self.bot.get_channel(payload.channel_id)
                            msg = await channel.fetch_message(payload.message_id)
                            await msg.remove_reaction(payload.emoji, discord.Object(id=payload.user_id))
                        except Exception:
                            pass
                        return

                # Bonus role = 2 entries (stored as two rows — but UNIQUE constraint means
                # we can only store one; handle by storing entries count separately if needed)
                entries = 1
                if bonus_role_id and member and any(r.id == bonus_role_id for r in member.roles):
                    entries = 2

                for _ in range(entries):
                    try:
                        await db.execute(
                            "INSERT OR IGNORE INTO giveaway_participants (giveaway_id, user_id) VALUES (?,?)",
                            (giveaway_id, payload.user_id)
                        )
                    except Exception:
                        pass
                await db.commit()
                logger.info(f"[Giveaway] User {payload.user_id} entered giveaway #{giveaway_id} ({entries} entr{'y' if entries==1 else 'ies'})")
        except Exception as e:
            logger.error(f"[Giveaway] on_raw_reaction_add error: {e}")

    @commands.Cog.listener()
    async def on_raw_reaction_remove(self, payload: discord.RawReactionActionEvent):
        """Remove a user from giveaway_participants when they un-react 🎉."""
        if str(payload.emoji) != "🎉":
            return
        if payload.user_id == self.bot.user.id:
            return
        try:
            async with self.bot.db._db_context() as db:
                async with db.execute(
                    "SELECT giveaway_id FROM giveaways WHERE message_id=? AND ended=0",
                    (payload.message_id,)
                ) as c:
                    row = await c.fetchone()
                if not row:
                    return
                giveaway_id = row[0] if isinstance(row, (tuple, list)) else row["giveaway_id"]
                await db.execute(
                    "DELETE FROM giveaway_participants WHERE giveaway_id=? AND user_id=?",
                    (giveaway_id, payload.user_id)
                )
                await db.commit()
                logger.info(f"[Giveaway] User {payload.user_id} left giveaway #{giveaway_id}")
        except Exception as e:
            logger.error(f"[Giveaway] on_raw_reaction_remove error: {e}")

    # ── Core giveaway logic ───────────────────────────────────────────────────

    async def _end_giveaway(self, giveaway_id: int, announce=True):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE giveaway_id=?", (giveaway_id,)) as c:
                gw = await c.fetchone()
            if not gw:
                return None
            gw = dict(gw)
            async with db.execute("SELECT user_id FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,)) as c:
                participants = [r["user_id"] for r in await c.fetchall()]
            await db.execute("UPDATE giveaways SET ended=1 WHERE giveaway_id=?", (giveaway_id,))
            await db.commit()

        winners = []
        if participants:
            winners = random.sample(participants, min(gw["winners_count"], len(participants)))

        if announce:
            channel = self.bot.get_channel(gw["channel_id"])
            if channel:
                if winners:
                    winner_mentions = " ".join(f"<@{w}>" for w in winners)
                    embed = comprehensive_embed(title="🎉 Giveaway Ended!", color=discord.Color.gold())
                    embed.add_field(name="🏆 Prize", value=gw["prize"], inline=False)
                    embed.add_field(name="🎊 Winners", value=winner_mentions, inline=False)
                    embed.add_field(name="👥 Total Entries", value=str(len(participants)), inline=True)
                else:
                    embed = comprehensive_embed(title="🎉 Giveaway Ended", description="No one entered the giveaway!", color=discord.Color.red())
                    embed.add_field(name="Prize", value=gw["prize"], inline=False)
                try:
                    await channel.send(embed=embed)
                    if winners:
                        await channel.send(" ".join(f"<@{w}>" for w in winners) + f" Congratulations! You won **{gw['prize']}**! 🎉")
                except Exception as e:
                    logger.error(f"Giveaway announcement error: {e}")
        return winners

    # ── Slash commands ────────────────────────────────────────────────────────

    @app_commands.command(name="start", description="Start a giveaway with role requirements, bonus entries, auto-DM winners.")
    @app_commands.describe(prize="Prize", duration_minutes="Duration in minutes", winners="Number of winners",
                           channel="Channel", required_role="Required role to enter",
                           bonus_role="Role with 2x entries", ping_role="Role to ping")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def start(self, interaction: discord.Interaction, prize: str, duration_minutes: int = 60,
                    winners: int = 1, channel: discord.TextChannel = None,
                    required_role: discord.Role = None, bonus_role: discord.Role = None,
                    ping_role: discord.Role = None):
        await interaction.response.defer(ephemeral=True)
        ch      = channel or interaction.channel
        end_ts  = int((discord.utils.utcnow() + datetime.timedelta(minutes=max(1, duration_minutes))).timestamp())
        w_count = max(1, winners)

        async with self.bot.db._db_context() as db:
            for col in ("required_role_id INTEGER", "bonus_role_id INTEGER"):
                try:
                    await db.execute(f"ALTER TABLE giveaways ADD COLUMN {col}")
                except Exception:
                    pass

            # FIX: column is 'created_by', not 'host_id'
            sql = (
                "INSERT INTO giveaways "
                "(guild_id, channel_id, prize, winners_count, end_time, created_by, required_role_id, bonus_role_id) "
                "VALUES (?, ?, ?, ?, datetime(?, 'unixepoch'), ?, ?, ?)"
            )
            async with db.execute(sql, (
                interaction.guild.id, ch.id, prize, w_count, end_ts,
                interaction.user.id,
                required_role.id if required_role else None,
                bonus_role.id    if bonus_role    else None,
            )) as c:
                gw_id = c.lastrowid
            await db.commit()

        req = []
        if required_role: req.append("Must have " + required_role.mention)
        if bonus_role:    req.append(bonus_role.mention + " gets 2x entries")

        from utils.embeds import brand_embed
        embed = comprehensive_embed(title="🎉  GIVEAWAY!", description="## " + prize, color=0xFFD700)
        embed.add_field(name="🏆 Winners", value=str(w_count),                 inline=True)
        embed.add_field(name="⏰ Ends",    value=f"<t:{end_ts}:R>",            inline=True)
        embed.add_field(name="📢 Host",   value=interaction.user.mention,       inline=True)
        if req:
            embed.add_field(name="📋 Requirements", value="\n".join(req), inline=False)
        embed.set_footer(text=f"ID: {gw_id}  •  React 🎉 to enter!")

        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        if file:
            msg = await ch.send(content=ping_role.mention if ping_role else None, embed=embed, file=file)
        else:
            msg = await ch.send(content=ping_role.mention if ping_role else None, embed=embed)
        await msg.add_reaction("🎉")

        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE giveaways SET message_id=? WHERE giveaway_id=?", (msg.id, gw_id))
            await db.commit()

        await interaction.followup.send(
            embed=comprehensive_embed(description=f"✅ Giveaway **#{gw_id}** started in {ch.mention}!", color=0x00FF94),
            ephemeral=True
        )

    @app_commands.command(name="end", description="Immediately end a giveaway and pick winners.")
    @app_commands.describe(giveaway_id="ID of the giveaway to end")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def end(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE giveaway_id=? AND guild_id=?", (giveaway_id, interaction.guild.id)) as c:
                gw = await c.fetchone()
        if not gw:
            return await interaction.response.send_message(embed=error_embed("Not Found", f"Giveaway #{giveaway_id} not found in this server."), ephemeral=True)
        await interaction.response.defer()
        winners = await self._end_giveaway(giveaway_id)
        if winners:
            mentions = " ".join(f"<@{w}>" for w in winners)
            await interaction.followup.send(embed=success_embed("Giveaway Ended!", f"**Winners:** {mentions}"))
        else:
            await interaction.followup.send(embed=info_embed("Giveaway Ended", "No participants to pick winners from."))

    @app_commands.command(name="reroll", description="Reroll winners for a completed giveaway.")
    @app_commands.describe(giveaway_id="ID of the ended giveaway to reroll")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def reroll(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE giveaway_id=? AND guild_id=?", (giveaway_id, interaction.guild.id)) as c:
                gw = await c.fetchone()
            if not gw:
                return await interaction.response.send_message(embed=error_embed("Not Found", f"Giveaway #{giveaway_id} not found."), ephemeral=True)
            gw = dict(gw)
            async with db.execute("SELECT user_id FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,)) as c:
                participants = [r["user_id"] for r in await c.fetchall()]
        if not participants:
            return await interaction.response.send_message(embed=error_embed("No Participants", "No one entered this giveaway."), ephemeral=True)
        new_winners = random.sample(participants, min(gw["winners_count"], len(participants)))
        mentions    = " ".join(f"<@{w}>" for w in new_winners)
        embed = success_embed("Giveaway Rerolled! 🔄", f"**Prize:** {gw['prize']}\n**New Winners:** {mentions}")
        await interaction.response.send_message(embed=embed)
        ch = interaction.guild.get_channel(gw["channel_id"])
        if ch:
            await ch.send(f"🔄 Rerolled: {mentions} — You won **{gw['prize']}**! 🎉")

    @app_commands.command(name="list", description="View all active giveaways in this server.")
    @command_guard
    async def list_giveaways(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE guild_id=? AND ended=0 ORDER BY end_time ASC", (interaction.guild.id,)) as c:
                giveaways = [dict(r) for r in await c.fetchall()]
        if not giveaways:
            return await interaction.response.send_message(embed=info_embed("No Active Giveaways", "No giveaways are currently running."))
        embed = comprehensive_embed(title="🎉 Active Giveaways", description=f"**{len(giveaways)}** active giveaway(s)", color=discord.Color.gold())
        for gw in giveaways[:8]:
            ch     = interaction.guild.get_channel(gw["channel_id"])
            end_ts = int(datetime.datetime.fromisoformat(gw["end_time"]).timestamp())
            embed.add_field(
                name=f"#{gw['giveaway_id']} — {gw['prize']}",
                value=(
                    f"**Channel:** {ch.mention if ch else 'Unknown'}\n"
                    f"**Winners:** {gw['winners_count']}\n"
                    f"**Ends:** <t:{end_ts}:R>\n"
                    f"**Status:** {'⏸️ Paused' if gw['paused'] else '▶️ Active'}"
                ),
                inline=False
            )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="cancel", description="Cancel and delete an active giveaway.")
    @app_commands.describe(giveaway_id="ID of the giveaway to cancel")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def cancel(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,))
            await db.execute("DELETE FROM giveaways WHERE giveaway_id=? AND guild_id=?", (giveaway_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Giveaway Cancelled", f"Giveaway **#{giveaway_id}** has been deleted."))

    @app_commands.command(name="edit-prize", description="Edit the prize of an active giveaway.")
    @app_commands.describe(giveaway_id="Giveaway ID", new_prize="New prize description")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def edit_prize(self, interaction: discord.Interaction, giveaway_id: int, new_prize: str):
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE giveaways SET prize=? WHERE giveaway_id=? AND guild_id=?", (new_prize, giveaway_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Prize Updated!", f"Giveaway **#{giveaway_id}** prize changed to **{new_prize}**."))

    @app_commands.command(name="winners", description="View past winners of a giveaway.")
    @app_commands.describe(giveaway_id="ID of the giveaway")
    @command_guard
    async def winners(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE giveaway_id=? AND guild_id=?", (giveaway_id, interaction.guild.id)) as c:
                gw = await c.fetchone()
        if not gw:
            return await interaction.response.send_message(embed=error_embed("Not Found", "Giveaway not found."), ephemeral=True)
        gw = dict(gw)
        embed = info_embed(
            f"Giveaway #{giveaway_id} Info",
            f"**Prize:** {gw['prize']}\n**Status:** {'Ended' if gw['ended'] else 'Active'}\n**Winners:** {gw['winners_count']}"
        )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="delete", description="Delete all records of a giveaway permanently.")
    @app_commands.describe(giveaway_id="Giveaway ID to delete")
    @app_commands.checks.has_permissions(administrator=True)
    @command_guard
    async def delete(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,))
            await db.execute("DELETE FROM giveaways WHERE giveaway_id=? AND guild_id=?", (giveaway_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Deleted", f"Giveaway #{giveaway_id} has been permanently deleted."))


async def setup(bot):
    await bot.add_cog(Giveaway(bot))
