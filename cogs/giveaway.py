"""
XERO Bot — Giveaway System
Button-based entry, two custom images (panel + winner), days/hours/minutes duration.
"""
import discord
import logging
import datetime
import random
import time
import aiosqlite
from discord.ext import commands, tasks
from discord import app_commands
from utils.guard import command_guard
from typing import Optional

logger = logging.getLogger("XERO.Giveaway")

GW_GOLD  = 0xF0B429
GW_ENDED = 0x4B4F58
GW_WIN   = 0x43B581


# ── Embed helpers ──────────────────────────────────────────────────────────────

def _active_embed(prize, end_ts, winners_count, host_mention,
                  entry_count=0, gw_id=None, required_role=None,
                  bonus_role=None, panel_image_url=None, note=None):
    embed = discord.Embed(color=GW_GOLD, timestamp=discord.utils.utcnow())
    embed.description = f"## {prize}"
    if note:
        embed.description += f"\n\n{note}"
    embed.add_field(name="🏆  Winners",   value=f"`{winners_count}`",                                inline=True)
    embed.add_field(name="⏱️  Ends",      value=f"<t:{end_ts}:R>",                                  inline=True)
    embed.add_field(name="🎫  Hosted by", value=host_mention,                                        inline=True)
    reqs = []
    if required_role: reqs.append(f"Must have {required_role.mention}")
    if bonus_role:    reqs.append(f"{bonus_role.mention} → **2× entries**")
    if reqs:
        embed.add_field(name="📋  Requirements", value="\n".join(reqs), inline=False)
    embed.add_field(
        name  = "🎟️  Entries",
        value = f"**{entry_count}** {'person has' if entry_count == 1 else 'people have'} entered",
        inline= False,
    )
    if panel_image_url:
        embed.set_image(url=panel_image_url)
    embed.set_footer(text=f"XERO ELITE  •  Giveaway #{gw_id}" if gw_id else "XERO ELITE  •  xero.gg")
    return embed


def _ended_embed(prize, winners, entry_count, gw_id=None, panel_image_url=None):
    embed = discord.Embed(
        color       = GW_WIN if winners else GW_ENDED,
        title       = "🎉  GIVEAWAY ENDED",
        description = f"**{prize}**",
        timestamp   = discord.utils.utcnow(),
    )
    if winners:
        embed.add_field(name="🏆  Winner(s)", value=" ".join(f"<@{w}>" for w in winners), inline=False)
    else:
        embed.add_field(name="😔  No entries", value="No one entered. Better luck next time!", inline=False)
    embed.add_field(name="📊  Total Entries", value=f"**{entry_count}**", inline=True)
    if panel_image_url:
        embed.set_thumbnail(url=panel_image_url)
    embed.set_footer(text=f"XERO ELITE  •  Giveaway #{gw_id}" if gw_id else "XERO ELITE  •  xero.gg")
    return embed


def _winner_announce_embed(prize, winners, entry_count, winner_image_url=None, gw_id=None):
    """Channel announcement embed shown when giveaway ends — uses the winner image."""
    embed = discord.Embed(
        color       = GW_WIN,
        title       = "🎉  We Have Winners!",
        description = f"**{prize}**\n\n" + " ".join(f"<@{w}>" for w in winners),
        timestamp   = discord.utils.utcnow(),
    )
    embed.add_field(name="Total Entries", value=str(entry_count), inline=True)
    if winner_image_url:
        embed.set_image(url=winner_image_url)
    embed.set_footer(text=f"XERO ELITE  •  Giveaway #{gw_id}" if gw_id else "XERO ELITE  •  xero.gg")
    return embed


def _winner_dm_embed(prize, channel_mention, guild_name, winner_image_url=None):
    """DM sent to each winner — includes the winner image if set."""
    embed = discord.Embed(
        color       = GW_WIN,
        title       = "🎉  You Won a Giveaway!",
        description = f"Congratulations! You were selected as a winner for\n**{prize}**",
        timestamp   = discord.utils.utcnow(),
    )
    embed.add_field(name="📍  Server",  value=guild_name,      inline=True)
    embed.add_field(name="📢  Channel", value=channel_mention, inline=True)
    if winner_image_url:
        embed.set_image(url=winner_image_url)
    embed.set_footer(text="XERO ELITE  •  Congratulations!")
    return embed


def _reroll_embed(prize, new_winners, rerolled_by, winner_image_url=None, gw_id=None):
    embed = discord.Embed(
        color       = GW_WIN,
        title       = "🎲  Reroll — New Winners!",
        description = f"**{prize}**\n\n" + " ".join(f"<@{w}>" for w in new_winners),
        timestamp   = discord.utils.utcnow(),
    )
    if winner_image_url:
        embed.set_image(url=winner_image_url)
    embed.set_footer(text=f"XERO ELITE  •  Rerolled by {rerolled_by}")
    return embed


# ── Persistent entry View ──────────────────────────────────────────────────────

class GiveawayEntryView(discord.ui.View):
    def __init__(self, gw_id, bot, entry_count=0):
        super().__init__(timeout=None)
        self.gw_id = gw_id
        self.bot   = bot

        btn = discord.ui.Button(
            label     = self._label(entry_count),
            style     = discord.ButtonStyle.success,
            custom_id = f"gw_enter:{gw_id}",
            emoji     = "🎟️",
        )
        btn.callback = self._enter_callback
        self.add_item(btn)

    @staticmethod
    def _label(count):
        return f"Enter  ·  {count} Entered" if count else "Enter Giveaway"

    def _update_label(self, count):
        for item in self.children:
            if isinstance(item, discord.ui.Button):
                item.label = self._label(count)

    async def _enter_callback(self, interaction):
        gw_id = self.gw_id
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT prize, required_role_id, bonus_role_id, ended, paused FROM giveaways WHERE giveaway_id=?",
                (gw_id,),
            ) as c:
                gw = await c.fetchone()

            if not gw:
                return await interaction.response.send_message("This giveaway no longer exists.", ephemeral=True)
            gw = dict(gw)

            if gw["ended"]:
                return await interaction.response.send_message("This giveaway has already ended.", ephemeral=True)
            if gw.get("paused"):
                return await interaction.response.send_message("This giveaway is currently paused.", ephemeral=True)

            # Required role check
            req_id = gw.get("required_role_id")
            if req_id:
                member = interaction.guild.get_member(interaction.user.id)
                if not member or not any(r.id == req_id for r in member.roles):
                    role = interaction.guild.get_role(req_id)
                    return await interaction.response.send_message(
                        f"You need the **{role.name if role else 'required'}** role to enter.",
                        ephemeral=True,
                    )

            # Check if already entered — no withdrawal, one-way entry
            async with db.execute(
                "SELECT COUNT(*) FROM giveaway_participants WHERE giveaway_id=? AND user_id=?",
                (gw_id, interaction.user.id),
            ) as c:
                already = (await c.fetchone())[0]

            if already:
                return await interaction.response.send_message(
                    f"✅ You're already entered in **{gw['prize']}**! Good luck!",
                    ephemeral=True,
                )

            # Enter — bonus role gets 2× entries (2 weighted rows)
            bonus_id = gw.get("bonus_role_id")
            entries  = 1
            if bonus_id:
                m = interaction.guild.get_member(interaction.user.id)
                if m and any(r.id == bonus_id for r in m.roles):
                    entries = 2
            for _ in range(entries):
                try:
                    await db.execute(
                        "INSERT INTO giveaway_participants (giveaway_id, user_id) VALUES (?,?)",
                        (gw_id, interaction.user.id),
                    )
                except Exception:
                    pass

            await db.commit()

            async with db.execute(
                "SELECT COUNT(DISTINCT user_id) FROM giveaway_participants WHERE giveaway_id=?",
                (gw_id,),
            ) as c:
                row = await c.fetchone()
            new_count = row[0] if row else 0

        # Update button label with new count
        self._update_label(new_count)

        # Update the embed's Entries field live on the panel
        embed = None
        if interaction.message and interaction.message.embeds:
            embed = interaction.message.embeds[0]
            for i, field in enumerate(embed.fields):
                if "Entries" in field.name or "🎟" in field.name:
                    embed.set_field_at(
                        i,
                        name  = field.name,
                        value = f"**{new_count}** {'person has' if new_count == 1 else 'people have'} entered",
                        inline= field.inline,
                    )
                    break

        bonus_note = " You have **2× entries** thanks to your role!" if entries == 2 else ""
        reply = f"✅ You've entered **{gw['prize']}**!{bonus_note}"

        if embed:
            await interaction.response.edit_message(embed=embed, view=self)
        else:
            await interaction.response.edit_message(view=self)
        await interaction.followup.send(reply, ephemeral=True)


# ── Cog ────────────────────────────────────────────────────────────────────────

class Giveaway(commands.GroupCog, name="giveaway"):
    def __init__(self, bot):
        self.bot = bot
        self.process_giveaways.start()
        self._restore_views.start()

    def cog_unload(self):
        self.process_giveaways.cancel()
        self._restore_views.cancel()

    @tasks.loop(count=1)
    async def _restore_views(self):
        """Re-register persistent button views for all active giveaways after bot is ready."""
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT giveaway_id FROM giveaways WHERE ended=0 AND message_id IS NOT NULL"
                ) as c:
                    rows = [dict(r) for r in await c.fetchall()]

            for row in rows:
                gid = row["giveaway_id"]
                async with self.bot.db._db_context() as db:
                    async with db.execute(
                        "SELECT COUNT(DISTINCT user_id) FROM giveaway_participants WHERE giveaway_id=?", (gid,)
                    ) as c:
                        cnt_row = await c.fetchone()
                cnt = cnt_row[0] if cnt_row else 0
                view = GiveawayEntryView(gw_id=gid, bot=self.bot, entry_count=cnt)
                self.bot.add_view(view)

            logger.info(f"[Giveaway] Restored {len(rows)} persistent views.")
        except Exception as e:
            logger.error(f"[Giveaway] view restore error: {e}")

    @_restore_views.before_loop
    async def _before_restore(self):
        await self.bot.wait_until_ready()

    @tasks.loop(minutes=1)
    async def process_giveaways(self):
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM giveaways WHERE ended=0 AND paused=0 AND end_time <= datetime('now')"
                ) as c:
                    rows = [dict(r) for r in await c.fetchall()]
            for gw in rows:
                await self._end_giveaway(gw["giveaway_id"])
        except Exception as e:
            logger.error(f"[Giveaway] loop: {e}")

    @process_giveaways.before_loop
    async def _before(self):
        await self.bot.wait_until_ready()

    # ── Core ─────────────────────────────────────────────────────────────────

    async def _end_giveaway(self, giveaway_id):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE giveaway_id=?", (giveaway_id,)) as c:
                gw = await c.fetchone()
            if not gw:
                return None
            gw = dict(gw)

            async with db.execute(
                "SELECT DISTINCT user_id FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,)
            ) as c:
                unique_ids = [r["user_id"] for r in await c.fetchall()]

            async with db.execute(
                "SELECT user_id FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,)
            ) as c:
                weighted = [r["user_id"] for r in await c.fetchall()]

            await db.execute("UPDATE giveaways SET ended=1 WHERE giveaway_id=?", (giveaway_id,))
            await db.commit()

        winners = []
        if weighted:
            seen, pool = set(), list(weighted)
            while len(winners) < gw["winners_count"] and pool:
                pick = random.choice(pool)
                if pick not in seen:
                    seen.add(pick)
                    winners.append(pick)
                pool.remove(pick)

        channel       = self.bot.get_channel(gw["channel_id"])
        panel_img     = gw.get("panel_image_url")
        winner_img    = gw.get("winner_image_url")

        # Edit the original giveaway message → ended state
        if gw.get("message_id") and channel:
            try:
                msg = await channel.fetch_message(gw["message_id"])
                ended = _ended_embed(gw["prize"], winners, len(unique_ids), giveaway_id, panel_img)
                dead  = discord.ui.View()
                dead.add_item(discord.ui.Button(
                    label    = "Giveaway Ended",
                    style    = discord.ButtonStyle.secondary,
                    disabled = True,
                    emoji    = "🔒",
                ))
                await msg.edit(embed=ended, view=dead)
            except Exception as e:
                logger.error(f"[Giveaway] edit original: {e}")

        if not channel:
            return winners

        # Announcement
        if winners:
            announce = _winner_announce_embed(gw["prize"], winners, len(unique_ids), winner_img, giveaway_id)
            mentions = " ".join(f"<@{w}>" for w in winners)
            await channel.send(content=mentions, embed=announce)

            # DM each winner
            for uid in winners:
                try:
                    m = channel.guild.get_member(uid)
                    if m:
                        dm = _winner_dm_embed(gw["prize"], channel.mention, channel.guild.name, winner_img)
                        await m.send(embed=dm)
                except Exception:
                    pass
        else:
            no_w = discord.Embed(
                color       = GW_ENDED,
                description = f"**{gw['prize']}** ended with no entries.",
                timestamp   = discord.utils.utcnow(),
            )
            no_w.set_footer(text=f"XERO ELITE  •  Giveaway #{giveaway_id}")
            await channel.send(embed=no_w)

        return winners

    # ── Commands ──────────────────────────────────────────────────────────────

    @app_commands.command(name="start", description="Start a giveaway with images, role requirements, and flexible duration.")
    @app_commands.describe(
        prize          = "What are you giving away?",
        days           = "Duration — days (default 0)",
        hours          = "Duration — hours (default 0)",
        minutes        = "Duration — minutes (default 0)",
        winners        = "Number of winners (default 1)",
        channel        = "Channel to post in (default: current channel)",
        required_role  = "Role required to enter",
        bonus_role     = "Role that gets 2× entries",
        ping_role      = "Role to ping when giveaway starts",
        panel_image    = "Upload an image shown IN the giveaway panel (prize photo, etc.)",
        panel_image_url= "Or paste a URL for the panel image",
        winner_image   = "Upload an image sent to winners and announced when giveaway ends",
        winner_image_url="Or paste a URL for the winner image",
        note           = "Optional extra text shown in the giveaway",
    )
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def start(
        self,
        interaction: discord.Interaction,
        prize:            str,
        days:             int                       = 0,
        hours:            int                       = 0,
        minutes:          int                       = 0,
        winners:          int                       = 1,
        channel:          Optional[discord.TextChannel] = None,
        required_role:    Optional[discord.Role]    = None,
        bonus_role:       Optional[discord.Role]    = None,
        ping_role:        Optional[discord.Role]    = None,
        panel_image:      Optional[discord.Attachment] = None,
        panel_image_url:  Optional[str]             = None,
        winner_image:     Optional[discord.Attachment] = None,
        winner_image_url: Optional[str]             = None,
        note:             Optional[str]             = None,
    ):
        await interaction.response.defer(ephemeral=True)

        total_minutes = days * 1440 + hours * 60 + minutes
        if total_minutes < 1:
            return await interaction.followup.send(
                "Please set a duration of at least 1 minute (e.g. `minutes:5`).", ephemeral=True
            )

        ch      = channel or interaction.channel
        end_ts  = int(time.time()) + (total_minutes * 60)
        w_count = max(1, winners)

        # Resolve images — uploads take priority over URLs
        final_panel  = None
        final_winner = None

        if panel_image:
            if not panel_image.content_type or not panel_image.content_type.startswith("image/"):
                return await interaction.followup.send("Panel image must be an image file (PNG, JPG, GIF, WebP).", ephemeral=True)
            final_panel = panel_image.url
        elif panel_image_url:
            final_panel = panel_image_url

        if winner_image:
            if not winner_image.content_type or not winner_image.content_type.startswith("image/"):
                return await interaction.followup.send("Winner image must be an image file (PNG, JPG, GIF, WebP).", ephemeral=True)
            final_winner = winner_image.url
        elif winner_image_url:
            final_winner = winner_image_url

        # Ensure DB columns exist
        async with self.bot.db._db_context() as db:
            for col in ("required_role_id INTEGER", "bonus_role_id INTEGER",
                        "panel_image_url TEXT", "winner_image_url TEXT"):
                try:
                    await db.execute(f"ALTER TABLE giveaways ADD COLUMN {col}")
                except Exception:
                    pass

            async with db.execute(
                "INSERT INTO giveaways "
                "(guild_id, channel_id, prize, winners_count, end_time, created_by, "
                " required_role_id, bonus_role_id, panel_image_url, winner_image_url) "
                "VALUES (?,?,?,?, datetime(?,'unixepoch'), ?,?,?,?,?)",
                (
                    interaction.guild.id, ch.id, prize, w_count, end_ts,
                    interaction.user.id,
                    required_role.id if required_role else None,
                    bonus_role.id    if bonus_role    else None,
                    final_panel,
                    final_winner,
                ),
            ) as c:
                gw_id = c.lastrowid
            await db.commit()

        embed = _active_embed(
            prize          = prize,
            end_ts         = end_ts,
            winners_count  = w_count,
            host_mention   = interaction.user.mention,
            entry_count    = 0,
            gw_id          = gw_id,
            required_role  = required_role,
            bonus_role     = bonus_role,
            panel_image_url= final_panel,
            note           = note,
        )

        view = GiveawayEntryView(gw_id=gw_id, bot=self.bot, entry_count=0)
        self.bot.add_view(view)

        msg = await ch.send(
            content = ping_role.mention if ping_role else None,
            embed   = embed,
            view    = view,
        )

        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE giveaways SET message_id=? WHERE giveaway_id=?", (msg.id, gw_id))
            await db.commit()

        # Duration display
        dur_parts = []
        if days:    dur_parts.append(f"{days}d")
        if hours:   dur_parts.append(f"{hours}h")
        if minutes: dur_parts.append(f"{minutes}m")
        dur_str = " ".join(dur_parts) or f"{total_minutes}m"

        confirm = discord.Embed(
            color       = GW_GOLD,
            title       = "Giveaway Started ✅",
            description = f"**{prize}** is live in {ch.mention}",
            timestamp   = discord.utils.utcnow(),
        )
        confirm.add_field(name="Duration",  value=dur_str,       inline=True)
        confirm.add_field(name="Ends",      value=f"<t:{end_ts}:F>", inline=True)
        confirm.add_field(name="Winners",   value=str(w_count),  inline=True)
        confirm.add_field(name="ID",        value=f"`{gw_id}`",  inline=True)
        if final_panel:  confirm.add_field(name="Panel Image",  value="✅ Set", inline=True)
        if final_winner: confirm.add_field(name="Winner Image", value="✅ Set", inline=True)
        confirm.set_footer(text="XERO ELITE  •  xero.gg")
        await interaction.followup.send(embed=confirm, ephemeral=True)

    @app_commands.command(name="end", description="End a giveaway immediately and draw winners.")
    @app_commands.describe(giveaway_id="Giveaway ID to end")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def end(self, interaction: discord.Interaction, giveaway_id: int):
        await interaction.response.defer(ephemeral=True)
        winners = await self._end_giveaway(giveaway_id)
        if winners is None:
            return await interaction.followup.send("Giveaway not found.", ephemeral=True)
        msg = (f"Giveaway #{giveaway_id} ended — **{len(winners)} winner(s)** drawn."
               if winners else f"Giveaway #{giveaway_id} ended — no entries.")
        await interaction.followup.send(
            embed=discord.Embed(color=GW_GOLD, description=f"✅ {msg}", timestamp=discord.utils.utcnow()),
            ephemeral=True,
        )

    @app_commands.command(name="reroll", description="Reroll winners for an ended giveaway.")
    @app_commands.describe(giveaway_id="Giveaway ID", count="How many to reroll (default 1)")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def reroll(self, interaction: discord.Interaction, giveaway_id: int, count: int = 1):
        await interaction.response.defer(ephemeral=True)
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE giveaway_id=?", (giveaway_id,)) as c:
                gw = await c.fetchone()
            if not gw:
                return await interaction.followup.send("Giveaway not found.", ephemeral=True)
            gw = dict(gw)
            async with db.execute(
                "SELECT user_id FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,)
            ) as c:
                pool = [r["user_id"] for r in await c.fetchall()]

        if not pool:
            return await interaction.followup.send("No participants to reroll from.", ephemeral=True)

        new_winners = random.sample(pool, min(count, len(pool)))
        channel     = self.bot.get_channel(gw["channel_id"])
        winner_img  = gw.get("winner_image_url")

        if channel:
            mentions = " ".join(f"<@{w}>" for w in new_winners)
            embed = _reroll_embed(gw["prize"], new_winners, interaction.user.display_name, winner_img, giveaway_id)
            await channel.send(content=mentions, embed=embed)
            for uid in new_winners:
                try:
                    m = channel.guild.get_member(uid)
                    if m:
                        await m.send(embed=_winner_dm_embed(gw["prize"], channel.mention, channel.guild.name, winner_img))
                except Exception:
                    pass

        await interaction.followup.send(
            embed=discord.Embed(color=GW_WIN, description=f"✅ Rerolled **{len(new_winners)}** winner(s)."),
            ephemeral=True,
        )

    @app_commands.command(name="pause", description="Pause a live giveaway — no new entries.")
    @app_commands.describe(giveaway_id="Giveaway ID")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def pause(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE giveaways SET paused=1 WHERE giveaway_id=? AND guild_id=?",
                             (giveaway_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(
            embed=discord.Embed(color=GW_GOLD, description=f"⏸  Giveaway #{giveaway_id} paused."),
            ephemeral=True,
        )

    @app_commands.command(name="resume", description="Resume a paused giveaway.")
    @app_commands.describe(giveaway_id="Giveaway ID")
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def resume(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE giveaways SET paused=0 WHERE giveaway_id=? AND guild_id=?",
                             (giveaway_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(
            embed=discord.Embed(color=GW_WIN, description=f"▶️  Giveaway #{giveaway_id} resumed."),
            ephemeral=True,
        )

    @app_commands.command(name="list", description="List all active giveaways in this server.")
    @command_guard
    async def list(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM giveaways WHERE guild_id=? AND ended=0 ORDER BY end_time ASC",
                (interaction.guild.id,),
            ) as c:
                rows = [dict(r) for r in await c.fetchall()]

        if not rows:
            return await interaction.followup.send(
                embed=discord.Embed(color=GW_ENDED, description="No active giveaways right now."),
                ephemeral=True,
            )

        embed = discord.Embed(color=GW_GOLD, title=f"Active Giveaways  ({len(rows)})", timestamp=discord.utils.utcnow())
        for gw in rows[:10]:
            try:
                end_ts = int(datetime.datetime.fromisoformat(gw["end_time"])
                             .replace(tzinfo=datetime.timezone.utc).timestamp())
            except Exception:
                end_ts = 0
            status = "⏸ Paused" if gw.get("paused") else (f"Ends <t:{end_ts}:R>" if end_ts else "Active")
            embed.add_field(
                name  = f"#{gw['giveaway_id']}  —  {gw['prize']}",
                value = f"{status}  ·  {gw['winners_count']} winner(s)  ·  <#{gw['channel_id']}>",
                inline= False,
            )
        embed.set_footer(text="XERO ELITE  •  xero.gg")
        await interaction.followup.send(embed=embed, ephemeral=True)

    @app_commands.command(name="info", description="Show full details about a giveaway.")
    @app_commands.describe(giveaway_id="Giveaway ID")
    @command_guard
    async def info(self, interaction: discord.Interaction, giveaway_id: int):
        await interaction.response.defer(ephemeral=True)
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM giveaways WHERE giveaway_id=?", (giveaway_id,)) as c:
                gw = await c.fetchone()
            if not gw:
                return await interaction.followup.send("Giveaway not found.", ephemeral=True)
            gw = dict(gw)
            async with db.execute(
                "SELECT COUNT(DISTINCT user_id) FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,)
            ) as c:
                cnt = (await c.fetchone())[0]

        try:
            end_ts = int(datetime.datetime.fromisoformat(gw["end_time"])
                         .replace(tzinfo=datetime.timezone.utc).timestamp())
        except Exception:
            end_ts = 0

        status = "Ended" if gw["ended"] else ("Paused" if gw.get("paused") else "Active")
        embed  = discord.Embed(
            color       = GW_ENDED if gw["ended"] else GW_GOLD,
            title       = f"Giveaway #{giveaway_id}",
            description = f"**{gw['prize']}**",
            timestamp   = discord.utils.utcnow(),
        )
        embed.add_field(name="Status",   value=status,                     inline=True)
        embed.add_field(name="Winners",  value=str(gw["winners_count"]),   inline=True)
        embed.add_field(name="Entries",  value=str(cnt),                   inline=True)
        embed.add_field(name="Ends",     value=f"<t:{end_ts}:F>" if end_ts else "—", inline=True)
        embed.add_field(name="Host",     value=f"<@{gw['created_by']}>",   inline=True)
        embed.add_field(name="Channel",  value=f"<#{gw['channel_id']}>",   inline=True)
        embed.add_field(name="Panel Image",  value="✅ Set" if gw.get("panel_image_url")  else "None", inline=True)
        embed.add_field(name="Winner Image", value="✅ Set" if gw.get("winner_image_url") else "None", inline=True)
        embed.set_footer(text="XERO ELITE  •  xero.gg")
        await interaction.followup.send(embed=embed, ephemeral=True)

    @app_commands.command(name="delete", description="Permanently delete a giveaway record.")
    @app_commands.describe(giveaway_id="Giveaway ID to delete")
    @app_commands.checks.has_permissions(administrator=True)
    @command_guard
    async def delete(self, interaction: discord.Interaction, giveaway_id: int):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM giveaway_participants WHERE giveaway_id=?", (giveaway_id,))
            await db.execute("DELETE FROM giveaways WHERE giveaway_id=? AND guild_id=?",
                             (giveaway_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(
            embed=discord.Embed(color=GW_GOLD, description=f"✅ Giveaway #{giveaway_id} permanently deleted."),
            ephemeral=True,
        )


async def setup(bot):
    await bot.add_cog(Giveaway(bot))
