from utils.guard import command_guard
"""
XERO Bot — Unified Configuration Dashboard
One command. One embed. Every setting.

/config → master dashboard with 12 feature panels
Each panel: sub-embed with all settings shown + buttons to change them
Back button on every sub-panel returns to master

Features covered:
  Welcome  · Farewell  · Logging  · Verification  · Tickets
  Moderation · AutoMod · Security · Leveling · Economy · AI · Server
"""
import discord, aiosqlite, logging, asyncio, re, io
from discord.ext import commands
from discord import app_commands
from utils.embeds import success_embed, error_embed, info_embed, XERO, comprehensive_embed

logger = logging.getLogger("XERO.Config")

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# HELPERS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def _ch(cid):   return f"<#{cid}>" if cid else "❌ Not set"
def _role(rid): return f"<@&{rid}>" if rid else "❌ Not set"
def _on(v, yes="✅ On", no="❌ Off"): return yes if v else no

async def _s(bot, guild_id):
    return await bot.db.get_guild_settings(guild_id) or {}

async def _set(bot, guild_id, key, val):
    await bot.db.update_guild_setting(guild_id, key, val)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODALS
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class ChannelModal(discord.ui.Modal):
    """Generic modal to pick channels by ID with validation."""
    def __init__(self, bot, guild, fields: list[tuple[str,str,str]], title="Set Channels"):
        super().__init__(title=title)
        self.bot    = bot
        self.guild  = guild
        self._fields = fields  # (db_key, label, placeholder)
        for _, label, placeholder in fields:
            self.add_item(discord.ui.TextInput(
                label=label, placeholder=placeholder,
                required=False, max_length=20
            ))

    async def on_submit(self, interaction: discord.Interaction):
        saved = []; errors = []
        for i, (key, label, _) in enumerate(self._fields):
            val = self.children[i].value.strip()
            if not val: continue
            try:
                cid = int(val)
                ch  = self.guild.get_channel(cid)
                if not ch: errors.append(f"`{label}`: channel not found"); continue
                await _set(self.bot, self.guild.id, key, cid)
                saved.append(f"**{label}:** {ch.mention}")
            except ValueError:
                errors.append(f"`{label}`: not a valid ID")
        lines = saved + ([f"⚠️ " + ", ".join(errors)] if errors else [])
        await interaction.response.send_message(
            embed=success_embed("✅  Channels Saved", "\n".join(lines) or "No changes."),
            ephemeral=True
        )


class RoleModal(discord.ui.Modal):
    def __init__(self, bot, guild, fields: list[tuple[str,str,str]], title="Set Roles"):
        super().__init__(title=title)
        self.bot    = bot
        self.guild  = guild
        self._fields = fields
        for _, label, placeholder in fields:
            self.add_item(discord.ui.TextInput(
                label=label, placeholder=placeholder,
                required=False, max_length=20
            ))

    async def on_submit(self, interaction: discord.Interaction):
        saved = []; errors = []
        for i, (key, label, _) in enumerate(self._fields):
            val = self.children[i].value.strip()
            if not val: continue
            try:
                rid  = int(val)
                role = self.guild.get_role(rid)
                if not role: errors.append(f"`{label}`: role not found"); continue
                await _set(self.bot, self.guild.id, key, rid)
                saved.append(f"**{label}:** {role.mention}")
            except ValueError:
                errors.append(f"`{label}`: not a valid ID")
        lines = saved + ([f"⚠️ " + ", ".join(errors)] if errors else [])
        await interaction.response.send_message(
            embed=success_embed("✅  Roles Saved", "\n".join(lines) or "No changes."),
            ephemeral=True
        )


class TextModal(discord.ui.Modal):
    def __init__(self, bot, guild_id, fields: list[tuple[str,str,str,bool]], title="Edit Text"):
        super().__init__(title=title)
        self.bot      = bot
        self.guild_id = guild_id
        self._fields  = fields  # (db_key, label, placeholder, is_paragraph)
        for _, label, placeholder, para in fields:
            self.add_item(discord.ui.TextInput(
                label=label, placeholder=placeholder,
                style=discord.TextStyle.paragraph if para else discord.TextStyle.short,
                required=False, max_length=1000
            ))

    async def on_submit(self, interaction: discord.Interaction):
        saved = []
        for i, (key, label, _, _) in enumerate(self._fields):
            val = self.children[i].value.strip()
            if val:
                await _set(self.bot, self.guild_id, key, val)
                saved.append(f"**{label}** saved")
        await interaction.response.send_message(
            embed=success_embed("✅  Saved", "\n".join(saved) or "No changes."),
            ephemeral=True
        )


class WelcomeMessageModal(discord.ui.Modal, title="Edit Welcome & Farewell Messages"):
    welcome_msg = discord.ui.TextInput(
        label="Welcome Message", style=discord.TextStyle.paragraph,
        placeholder="Welcome {user} to {server}! You are member #{count}.",
        required=False, max_length=800
    )
    farewell_msg = discord.ui.TextInput(
        label="Farewell Message", style=discord.TextStyle.paragraph,
        placeholder="Goodbye {name}! Thanks for being part of {server}.",
        required=False, max_length=800
    )
    def __init__(self, bot, guild):
        super().__init__()
        self.bot   = bot
        self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        saved = []
        if self.welcome_msg.value:
            await _set(self.bot, self.guild.id, "welcome_message", self.welcome_msg.value)
            saved.append("✅ Welcome message saved")
        if self.farewell_msg.value:
            await _set(self.bot, self.guild.id, "farewell_message", self.farewell_msg.value)
            saved.append("✅ Farewell message saved")
        await interaction.response.send_message(
            embed=success_embed("Messages Saved",
                "\n".join(saved) + "\n\n**Placeholders:** `{user}` `{name}` `{server}` `{count}`"
            ), ephemeral=True
        )


class WelcomeDMModal(discord.ui.Modal, title="Configure Welcome DM"):
    message = discord.ui.TextInput(
        label="DM Message", style=discord.TextStyle.paragraph,
        placeholder="Hey {name}! Welcome to {server}! Check out the channels and enjoy your stay!",
        max_length=800, required=True,
    )
    image_url = discord.ui.TextInput(
        label="DM Image URL (optional — use /config welcome-image to upload)",
        placeholder="Leave blank. Use /config welcome-image to upload an image file.",
        required=False, max_length=500,
    )
    def __init__(self, bot, guild):
        super().__init__()
        self.bot   = bot
        self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        await _set(self.bot, self.guild.id, "welcome_dm_message", self.message.value.strip())
        if self.image_url.value:
            await _set(self.bot, self.guild.id, "welcome_dm_image_url", self.image_url.value.strip())
        preview = (self.message.value
            .replace("{user}",   interaction.user.mention)
            .replace("{name}",   interaction.user.display_name)
            .replace("{server}", self.guild.name)
            .replace("{count}",  str(self.guild.member_count)))
        await interaction.response.send_message(
            embed=success_embed("DM Message Saved", f"**Preview:**\n{preview}"),
            ephemeral=True
        )


class AutoModModal(discord.ui.Modal, title="AutoMod Settings"):
    max_mentions = discord.ui.TextInput(label="Max Mentions per Message", placeholder="5", required=False, max_length=3)
    max_lines    = discord.ui.TextInput(label="Max Lines per Message",    placeholder="20", required=False, max_length=3)
    spam_limit   = discord.ui.TextInput(label="Spam Limit (msgs/10s)",   placeholder="5",  required=False, max_length=3)
    invite_action= discord.ui.TextInput(label="Invite Action (delete/warn/ban)", placeholder="delete", required=False, max_length=10)
    log_channel  = discord.ui.TextInput(label="AutoMod Log Channel ID",  placeholder="Paste channel ID", required=False, max_length=20)
    def __init__(self, bot, guild):
        super().__init__()
        self.bot = bot; self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        saved = []
        nums = [
            ("automod_max_mentions", self.max_mentions.value),
            ("automod_max_lines",    self.max_lines.value),
            ("automod_spam_limit",   self.spam_limit.value),
        ]
        for key, val in nums:
            if val.strip():
                try:
                    await _set(self.bot, self.guild.id, key, int(val.strip()))
                    saved.append(key.replace("automod_","").replace("_"," ").title())
                except ValueError: pass
        if self.invite_action.value.strip() in ("delete","warn","ban","kick"):
            await _set(self.bot, self.guild.id, "automod_invite_action", self.invite_action.value.strip())
            saved.append("Invite Action")
        if self.log_channel.value.strip():
            try:
                ch = self.guild.get_channel(int(self.log_channel.value.strip()))
                if ch:
                    await _set(self.bot, self.guild.id, "automod_log_channel_id", ch.id)
                    saved.append(f"Log → {ch.mention}")
            except ValueError: pass
        await interaction.response.send_message(
            embed=success_embed("AutoMod Updated", "Saved: " + (", ".join(saved) or "No changes")),
            ephemeral=True
        )


class SecurityModal(discord.ui.Modal, title="Security Settings"):
    min_age    = discord.ui.TextInput(label="Min Account Age (days, 0 = off)", placeholder="7", required=False, max_length=4)
    age_action = discord.ui.TextInput(label="Age Action (kick / ban / kick_dm)", placeholder="kick_dm", required=False, max_length=10)
    nuke_thresh= discord.ui.TextInput(label="Anti-Nuke Threshold (actions/60s)", placeholder="3", required=False, max_length=3)
    def __init__(self, bot, guild):
        super().__init__()
        self.bot = bot; self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        saved = []
        if self.min_age.value.strip():
            try:
                await _set(self.bot, self.guild.id, "min_account_age_days", int(self.min_age.value.strip()))
                saved.append("Min Account Age")
            except ValueError: pass
        if self.age_action.value.strip() in ("kick","ban","kick_dm","ban_dm"):
            await _set(self.bot, self.guild.id, "account_age_action", self.age_action.value.strip())
            saved.append("Age Action")
        if self.nuke_thresh.value.strip():
            try:
                await _set(self.bot, self.guild.id, "anti_nuke_threshold", int(self.nuke_thresh.value.strip()))
                saved.append("Anti-Nuke Threshold")
            except ValueError: pass
        await interaction.response.send_message(
            embed=success_embed("Security Updated", "Saved: " + (", ".join(saved) or "No changes")),
            ephemeral=True
        )


class LevelingModal(discord.ui.Modal, title="Leveling Settings"):
    voice_rate = discord.ui.TextInput(label="Voice XP per Minute (default 5)", placeholder="5", required=False, max_length=4)
    dm_msg     = discord.ui.TextInput(
        label="Level-Up DM Message (blank = off)",
        style=discord.TextStyle.paragraph,
        placeholder="Congrats {name}! You reached level {level} in {server}!",
        required=False, max_length=500
    )
    def __init__(self, bot, guild):
        super().__init__()
        self.bot = bot; self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        saved = []
        if self.voice_rate.value.strip():
            try:
                await _set(self.bot, self.guild.id, "voice_xp_rate", int(self.voice_rate.value.strip()))
                saved.append("Voice XP rate")
            except ValueError: pass
        if self.dm_msg.value.strip():
            await _set(self.bot, self.guild.id, "levelup_dm_message", self.dm_msg.value.strip())
            await _set(self.bot, self.guild.id, "levelup_dm_enabled", 1)
            saved.append("Level-up DM")
        await interaction.response.send_message(
            embed=success_embed("Leveling Updated", "Saved: " + (", ".join(saved) or "No changes")),
            ephemeral=True
        )


class VerificationModal(discord.ui.Modal, title="Verification Setup"):
    channel_id = discord.ui.TextInput(label="Verification Channel ID",   placeholder="Paste channel ID", required=True, max_length=20)
    role_id    = discord.ui.TextInput(label="Verified Role ID",          placeholder="Paste role ID",    required=True, max_length=20)
    message    = discord.ui.TextInput(
        label="Verification Message (optional)",
        style=discord.TextStyle.paragraph,
        placeholder="Click the button below to verify and gain access to the server.",
        required=False, max_length=500
    )
    def __init__(self, bot, guild):
        super().__init__()
        self.bot = bot; self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        try:
            ch   = self.guild.get_channel(int(self.channel_id.value.strip()))
            role = self.guild.get_role(int(self.role_id.value.strip()))
            if not ch:   return await interaction.response.send_message(embed=error_embed("Error","Channel not found."), ephemeral=True)
            if not role: return await interaction.response.send_message(embed=error_embed("Error","Role not found."),    ephemeral=True)
            msg = self.message.value.strip() or f"Welcome to **{self.guild.name}**! Click below to verify."
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "INSERT OR REPLACE INTO verification_config (guild_id, channel_id, role_id, message) VALUES (?,?,?,?)",
                    (self.guild.id, ch.id, role.id, msg)
                )
                await db.commit()
            await _set(self.bot, self.guild.id, "verify_channel_id", ch.id)
            await _set(self.bot, self.guild.id, "verify_role_id",    role.id)
            # Post verification panel
            verify_embed = discord.Embed(
                title="✅  Verification Required",
                description=msg,
                color=XERO.SUCCESS
            )
            verify_embed.set_footer(text=f"{self.guild.name}  •  Powered by XERO")
            view = _VerifyButtonView()
            await ch.send(embed=verify_embed, view=view)
            await interaction.response.send_message(
                embed=success_embed("Verification Set Up",
                    f"**Channel:** {ch.mention}\n**Role:** {role.mention}\n\n"
                    "Verification panel posted! Members click the button to get verified."
                ), ephemeral=True
            )
        except (ValueError, Exception) as e:
            await interaction.response.send_message(embed=error_embed("Failed", str(e)), ephemeral=True)


class TicketModal(discord.ui.Modal, title="Ticket System Setup"):
    channel_id  = discord.ui.TextInput(label="Ticket Panel Channel ID",   placeholder="Where to post the 'Open Ticket' button", required=True,  max_length=20)
    role_id     = discord.ui.TextInput(label="Support Role ID",           placeholder="Role that sees all tickets",             required=False, max_length=20)
    category_id = discord.ui.TextInput(label="Ticket Category ID",        placeholder="Category where ticket channels open",    required=False, max_length=20)
    panel_msg   = discord.ui.TextInput(
        label="Panel Message",
        style=discord.TextStyle.paragraph,
        placeholder="Need help? Click the button below to open a support ticket.",
        required=False, max_length=500
    )
    def __init__(self, bot, guild):
        super().__init__()
        self.bot = bot; self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        try:
            ch = self.guild.get_channel(int(self.channel_id.value.strip()))
            if not ch: return await interaction.response.send_message(embed=error_embed("Error","Channel not found."), ephemeral=True)
            if self.role_id.value.strip():
                role = self.guild.get_role(int(self.role_id.value.strip()))
                if role: await _set(self.bot, self.guild.id, "ticket_support_role_id", role.id)
            if self.category_id.value.strip():
                cat = self.guild.get_channel(int(self.category_id.value.strip()))
                if cat: await _set(self.bot, self.guild.id, "ticket_category_id", cat.id)
            msg = self.panel_msg.value.strip() or "Need help? Click the button below to open a support ticket."
            panel_embed = discord.Embed(
                title="🎫  Support Tickets",
                description=msg,
                color=XERO.PRIMARY
            )
            panel_embed.set_footer(text=f"{self.guild.name}  •  Powered by XERO")
            view = _TicketButtonView()
            await ch.send(embed=panel_embed, view=view)
            await interaction.response.send_message(
                embed=success_embed("Tickets Set Up",
                    f"Ticket panel posted in {ch.mention}!\n"
                    "Members can now open tickets by clicking the button."
                ), ephemeral=True
            )
        except (ValueError, Exception) as e:
            await interaction.response.send_message(embed=error_embed("Failed", str(e)), ephemeral=True)


class LoggingModal(discord.ui.Modal, title="Logging Channels"):
    unified  = discord.ui.TextInput(label="Unified Log (all events)",    placeholder="Channel ID — fills all below too", required=False, max_length=20)
    messages = discord.ui.TextInput(label="Message Logs",                 placeholder="Channel ID", required=False, max_length=20)
    members  = discord.ui.TextInput(label="Member Logs (joins/bans)",     placeholder="Channel ID", required=False, max_length=20)
    server   = discord.ui.TextInput(label="Server Logs (channels/roles)", placeholder="Channel ID", required=False, max_length=20)
    voice    = discord.ui.TextInput(label="Voice Logs",                   placeholder="Channel ID", required=False, max_length=20)
    def __init__(self, bot, guild):
        super().__init__()
        self.bot = bot; self.guild = guild
    async def on_submit(self, interaction: discord.Interaction):
        async def save_ch(key, raw):
            if not raw.strip(): return None
            try:
                ch = self.guild.get_channel(int(raw.strip()))
                if ch: await _set(self.bot, self.guild.id, key, ch.id); return ch
            except ValueError: pass
            return None
        saved = []
        if self.unified.value:
            ch = await save_ch("log_channel_id", self.unified.value)
            if ch:
                for k in ["message_log_channel_id","member_log_channel_id","server_log_channel_id","voice_log_channel_id"]:
                    await _set(self.bot, self.guild.id, k, ch.id)
                saved.append(f"All logs → {ch.mention}")
        for label, key, raw in [
            ("Messages", "message_log_channel_id", self.messages.value),
            ("Members",  "member_log_channel_id",  self.members.value),
            ("Server",   "server_log_channel_id",  self.server.value),
            ("Voice",    "voice_log_channel_id",   self.voice.value),
        ]:
            ch = await save_ch(key, raw)
            if ch: saved.append(f"{label} → {ch.mention}")
        # Clear cache
        adv = self.bot.cogs.get("AdvancedLogger")
        if adv: adv._cache.pop(self.guild.id, None)
        await interaction.response.send_message(
            embed=success_embed("Logging Updated", "\n".join(saved) or "No changes."),
            ephemeral=True
        )


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# PERSISTENT VIEWS (survive restart)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class _VerifyButtonView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)
    @discord.ui.button(label="✅  Verify Me", style=discord.ButtonStyle.success, custom_id="xero_verify_btn")
    async def verify(self, interaction: discord.Interaction, button: discord.ui.Button):
        bot = interaction.client
        try:
            async with bot.db._db_context() as db:
                async with db.execute("SELECT role_id FROM verification_config WHERE guild_id=?",
                                       (interaction.guild.id,)) as c:
                    row = await c.fetchone()
            if not row: return await interaction.response.send_message("❌ Verification not configured.", ephemeral=True)
            role = interaction.guild.get_role(row[0])
            if not role: return await interaction.response.send_message("❌ Verified role not found.", ephemeral=True)
            if role in interaction.user.roles:
                return await interaction.response.send_message("✅ You are already verified!", ephemeral=True)
            await interaction.user.add_roles(role, reason="XERO Verification")
            await interaction.response.send_message(
                embed=success_embed("✅  Verified!", f"You now have the **{role.name}** role. Welcome!"),
                ephemeral=True
            )
        except Exception as e:
            await interaction.response.send_message(f"❌ Error: {e}", ephemeral=True)


class _TicketButtonView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)
    @discord.ui.button(label="🎫  Open a Ticket", style=discord.ButtonStyle.primary, custom_id="xero_ticket_btn")
    async def open_ticket(self, interaction: discord.Interaction, button: discord.ui.Button):
        bot  = interaction.client
        guild = interaction.guild
        s    = await bot.db.get_guild_settings(guild.id) or {}
        cat_id = s.get("ticket_category_id")
        cat    = guild.get_channel(cat_id) if cat_id else None
        role_id = s.get("ticket_support_role_id")
        role    = guild.get_role(role_id) if role_id else None
        # Check for existing open ticket
        existing = discord.utils.get(guild.text_channels, name=f"ticket-{interaction.user.name.lower()[:20]}")
        if existing:
            return await interaction.response.send_message(
                f"❌ You already have an open ticket: {existing.mention}", ephemeral=True
            )
        overwrites = {
            guild.default_role:    discord.PermissionOverwrite(view_channel=False),
            interaction.user:      discord.PermissionOverwrite(view_channel=True, send_messages=True, read_message_history=True),
            guild.me:              discord.PermissionOverwrite(view_channel=True, send_messages=True, manage_channels=True),
        }
        if role: overwrites[role] = discord.PermissionOverwrite(view_channel=True, send_messages=True)
        try:
            ch = await guild.create_text_channel(
                name=f"ticket-{interaction.user.name[:20]}",
                category=cat, overwrites=overwrites,
                topic=f"Support ticket for {interaction.user} ({interaction.user.id})"
            )
            embed = discord.Embed(
                title=f"🎫  Ticket — {interaction.user.display_name}",
                description=(
                    f"Hello {interaction.user.mention}! A staff member will be with you shortly.\n\n"
                    f"**Please describe your issue in detail.**"
                ),
                color=XERO.PRIMARY
            )
            embed.set_footer(text="XERO Tickets  •  Use /ticket close to close this ticket")
            await ch.send(embed=embed)
            await interaction.response.send_message(f"✅ Ticket opened: {ch.mention}")
        except Exception as e:
            await interaction.response.send_message(f"❌ Failed: {e}", ephemeral=True)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SUB-PANEL VIEWS  (each is a full feature dashboard with ← Back)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class SubView(discord.ui.View):
    """Base class: every sub-panel has a back button that returns to master."""
    def __init__(self, bot, guild):
        super().__init__(timeout=300)
        self.bot   = bot
        self.guild = guild

    @discord.ui.button(label="← Back", style=discord.ButtonStyle.secondary, row=4)
    async def go_back(self, interaction: discord.Interaction, button: discord.ui.Button):
        embed, view = await MasterDashboard.build(self.bot, interaction.guild)
        await interaction.response.edit_message(embed=embed, view=view)


# ── Welcome ──────────────────────────────────────────────────────────────────
class WelcomePanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        e = comprehensive_embed(title="👋  Welcome System", color=XERO.SUCCESS)
        e.add_field(name="📢 Channel",      value=_ch(s.get("welcome_channel_id")),                    inline=True)
        e.add_field(name="📤 Farewell Ch",  value=_ch(s.get("farewell_channel_id")),                   inline=True)
        e.add_field(name="📨 Welcome DM",   value=_on(s.get("welcome_dm_enabled",0)),                  inline=True)
        e.add_field(name="🖼️ Card Image",  value="✅ Uploaded" if self._has_card() else "❌ None",     inline=True)
        e.add_field(name="🎨 Overlay",      value=s.get("welcome_card_overlay","gradient"),             inline=True)
        e.add_field(name="✏️ Name on Card", value=_on(s.get("welcome_card_show_name",1)),              inline=True)
        e.add_field(name="💬 Welcome Msg",  value=f"`{(s.get('welcome_message') or 'Default')[:60]}`", inline=False)
        e.set_footer(text="XERO Dashboard  •  👋 Welcome  •  Use buttons to configure")
        return e

    def _has_card(self):
        import os
        return os.path.exists(f"data/welcome_images/{self.guild.id}.png")

    @discord.ui.button(label="📢 Set Channels",    style=discord.ButtonStyle.primary,   row=0)
    async def set_channels(self, i, b):
        await i.response.send_message(embed=info_embed(
            "📢  Set Welcome & Farewell Channels",
            "Use these slash commands — Discord shows a **channel picker**, no ID needed:\n\n"
            "**`/config set-welcome #channel`** — set welcome channel\n"
            "**`/config set-farewell #channel`** — set farewell channel\n\n"
            "*Just type `/config set-welcome` and Discord will show all your channels to pick from.*"
        ))

    @discord.ui.button(label="✏️ Edit Messages",   style=discord.ButtonStyle.secondary, row=0)
    async def edit_msgs(self, i, b):
        await i.response.send_modal(WelcomeMessageModal(self.bot, self.guild))

    @discord.ui.button(label="📨 Toggle DM",       style=discord.ButtonStyle.success,   row=0)
    async def toggle_dm(self, i, b):
        s   = await _s(self.bot, self.guild.id)
        cur = s.get("welcome_dm_enabled", 0)
        await _set(self.bot, self.guild.id, "welcome_dm_enabled", 0 if cur else 1)
        e = await self.embed()
        await i.response.edit_message(embed=e, view=self)

    @discord.ui.button(label="📨 Set DM Message",  style=discord.ButtonStyle.secondary, row=1)
    async def set_dm(self, i, b):
        await i.response.send_modal(WelcomeDMModal(self.bot, self.guild))

    @discord.ui.button(label="🖼️ Upload Card",    style=discord.ButtonStyle.blurple,   row=1)
    async def upload_info(self, i, b):
        await i.response.send_message(embed=info_embed(
            "📤  How to Set Up Welcome Card",
            "**Step 1:** Use `/config set-welcome #channel` to set the channel\n"
            "**Step 2:** Use `/config welcome-upload` and attach your image file\n"
            "**Step 3:** Use `/config welcome-preview` to see the live preview\n\n"
            "The bot overlays the joining member's **name + circular avatar** on your image automatically.\n"
            "Every welcome message looks unique — their name is baked in."
        ))

    @discord.ui.button(label="✏️ Card Settings",  style=discord.ButtonStyle.secondary, row=1)
    async def card_settings(self, i, b):
        await i.response.send_message(embed=info_embed(
            "🎨  Welcome Card Settings",
            "Use **`/config welcome-upload`** and pick your settings:\n\n"
            "• **Name position:** Bottom left, center, top, etc.\n"
            "• **Text color:** Any hex color (#FFFFFF)\n"
            "• **Overlay style:** Gradient, bar, full, none\n"
            "• **Show/hide:** Name, avatar, member count\n\n"
            "Or just re-upload with new settings — it replaces instantly."
        ))

    @discord.ui.button(label="🔄 Refresh",         style=discord.ButtonStyle.secondary, row=2)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── Logging ───────────────────────────────────────────────────────────────────
class LoggingPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        e = comprehensive_embed(title="📋  Logging System", color=0xFFB800)
        e.add_field(name="🌐 Unified",   value=_ch(s.get("log_channel_id")),            inline=True)
        e.add_field(name="💬 Messages",  value=_ch(s.get("message_log_channel_id")),    inline=True)
        e.add_field(name="👥 Members",   value=_ch(s.get("member_log_channel_id")),     inline=True)
        e.add_field(name="🏰 Server",    value=_ch(s.get("server_log_channel_id")),     inline=True)
        e.add_field(name="🔊 Voice",     value=_ch(s.get("voice_log_channel_id")),      inline=True)
        e.add_field(name="🛡️ Webhooks", value=_on(s.get("webhook_protection_enabled")), inline=True)
        e.set_footer(text="XERO Dashboard  •  📋 Logging")
        return e

    @discord.ui.button(label="📋 Set Channels",   style=discord.ButtonStyle.primary,   row=0)
    async def set_channels(self, i, b):
        await i.response.send_message(embed=info_embed(
            "📋  Set Log Channels",
            "Use this slash command — Discord shows a **channel picker**:\n\n"
            "**`/config set-logs`** — set all log channels\n\n"
            "Options: `unified` (one channel for everything), or separate channels for\n"
            "`messages`, `members`, `server`, `voice`\n\n"
            "*Just type `/config set-logs` and pick channels from the dropdown.*"
        ))

    @discord.ui.button(label="🛡️ Webhook Guard", style=discord.ButtonStyle.success,   row=0)
    async def webhook_guard(self, i, b):
        s   = await _s(self.bot, self.guild.id)
        cur = s.get("webhook_protection_enabled", 0)
        await _set(self.bot, self.guild.id, "webhook_protection_enabled", 0 if cur else 1)
        adv = self.bot.cogs.get("AdvancedLogger")
        if adv: adv._cache.pop(self.guild.id, None)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="🧪 Test Logs",      style=discord.ButtonStyle.secondary, row=0)
    async def test_logs(self, i, b):
        await i.response.defer(ephemeral=True)
        adv  = self.bot.cogs.get("AdvancedLogger")
        sent = []
        if adv:
            for lt in ["msg_edit","join","ch_create","voice","role_create"]:
                ch = await adv._ch(self.guild, lt)
                if ch and ch.id not in sent:
                    try:
                        te = comprehensive_embed(title="🧪 XERO Logging Test", description="✅ Log channel confirmed and working.", color=XERO.PRIMARY)
                        await ch.send(embed=te); sent.append(ch.id)
                    except Exception: pass
        result = f"Tests sent to {len(sent)} channel(s)." if sent else "No log channels set yet."
        await i.followup.send(embed=success_embed("Test Complete", result))

    @discord.ui.button(label="🔄 Refresh",         style=discord.ButtonStyle.secondary, row=1)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── Verification ───────────────────────────────────────────────────────────────
class VerificationPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT channel_id, role_id, message FROM verification_config WHERE guild_id=?",
                                  (self.guild.id,)) as c:
                vc = await c.fetchone()
        e = comprehensive_embed(title="✅  Verification System", color=XERO.SUCCESS)
        if vc:
            e.add_field(name="📢 Channel",   value=_ch(vc[0]),           inline=True)
            e.add_field(name="🎭 Role",      value=_role(vc[1]),          inline=True)
            e.add_field(name="💬 Message",   value=f"`{vc[2][:80]}`",     inline=False)
            e.add_field(name="Status",       value="✅ Active",            inline=True)
        else:
            e.description = "❌ Not set up. Click **Setup Verification** below."
        e.set_footer(text="XERO Dashboard  •  ✅ Verification")
        return e

    @discord.ui.button(label="⚙️ Setup / Update",  style=discord.ButtonStyle.primary,   row=0)
    async def setup(self, i, b):
        await i.response.send_modal(VerificationModal(self.bot, self.guild))

    @discord.ui.button(label="🔄 Refresh",          style=discord.ButtonStyle.secondary, row=0)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── Tickets ───────────────────────────────────────────────────────────────────
class TicketsPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT COUNT(*) FROM tickets WHERE guild_id=? AND status='open'",
                                  (self.guild.id,)) as c:
                open_tix = (await c.fetchone())[0]
            async with db.execute("SELECT COUNT(*) FROM tickets WHERE guild_id=?",
                                  (self.guild.id,)) as c:
                total_tix = (await c.fetchone())[0]
        e = comprehensive_embed(title="🎫  Ticket System", color=XERO.PRIMARY)
        e.add_field(name="🎭 Support Role", value=_role(s.get("ticket_support_role_id")), inline=True)
        e.add_field(name="📁 Category",     value=_ch(s.get("ticket_category_id")),       inline=True)
        e.add_field(name="🎫 Open Tickets", value=str(open_tix),                           inline=True)
        e.add_field(name="📊 Total Ever",   value=str(total_tix),                          inline=True)
        e.set_footer(text="XERO Dashboard  •  🎫 Tickets")
        return e

    @discord.ui.button(label="⚙️ Setup / Post Panel", style=discord.ButtonStyle.primary,   row=0)
    async def setup(self, i, b):
        await i.response.send_modal(TicketModal(self.bot, self.guild))

    @discord.ui.button(label="🔄 Refresh",            style=discord.ButtonStyle.secondary, row=0)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── AutoMod ───────────────────────────────────────────────────────────────────
class AutoModPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        e = comprehensive_embed(title="🤖  AutoMod", color=0xFF6B35)
        e.add_field(name="Status",         value=_on(s.get("automod_enabled",0)),             inline=True)
        e.add_field(name="Anti-Spam",      value=_on(s.get("automod_anti_spam",0)),           inline=True)
        e.add_field(name="Anti-Caps",      value=_on(s.get("automod_anti_caps",0)),           inline=True)
        e.add_field(name="Anti-Links",     value=_on(s.get("automod_anti_links",0)),          inline=True)
        e.add_field(name="Max Mentions",   value=str(s.get("automod_max_mentions",5)),        inline=True)
        e.add_field(name="Spam Limit",     value=str(s.get("automod_spam_limit",5))+"/10s",  inline=True)
        e.add_field(name="📋 Log Channel", value=_ch(s.get("automod_log_channel_id")),        inline=True)
        e.set_footer(text="XERO Dashboard  •  🤖 AutoMod")
        return e

    @discord.ui.button(label="⚡ Toggle AutoMod",  style=discord.ButtonStyle.primary,   row=0)
    async def toggle(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "automod_enabled", 0 if s.get("automod_enabled",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Spam",     style=discord.ButtonStyle.secondary, row=0)
    async def toggle_spam(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "automod_anti_spam", 0 if s.get("automod_anti_spam",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Links",    style=discord.ButtonStyle.secondary, row=0)
    async def toggle_links(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "automod_anti_links", 0 if s.get("automod_anti_links",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Caps",     style=discord.ButtonStyle.secondary, row=1)
    async def toggle_caps(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "automod_anti_caps", 0 if s.get("automod_anti_caps",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚙️ Advanced Settings", style=discord.ButtonStyle.blurple, row=1)
    async def advanced(self, i, b):
        await i.response.send_modal(AutoModModal(self.bot, self.guild))

    @discord.ui.button(label="🔄 Refresh",          style=discord.ButtonStyle.secondary, row=2)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── Security ──────────────────────────────────────────────────────────────────
class SecurityPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        e = comprehensive_embed(title="🛡️  Security", color=0xFF1744)
        e.add_field(name="Anti-Nuke",     value=_on(s.get("anti_nuke_enabled",0)),             inline=True)
        e.add_field(name="Nuke Thresh",   value=f"{s.get('anti_nuke_threshold',3)}/60s",        inline=True)
        e.add_field(name="Role Restore",  value=_on(s.get("role_restore_enabled",0)),           inline=True)
        e.add_field(name="Link Filter",   value=_on(s.get("link_filter_enabled",0)),            inline=True)
        e.add_field(name="Min Acct Age",  value=f"{s.get('min_account_age_days',0)} days",     inline=True)
        e.add_field(name="Age Action",    value=s.get("account_age_action","kick_dm"),          inline=True)
        e.set_footer(text="XERO Dashboard  •  🛡️ Security")
        return e

    @discord.ui.button(label="⚡ Toggle Anti-Nuke",    style=discord.ButtonStyle.danger,     row=0)
    async def toggle_nuke(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "anti_nuke_enabled", 0 if s.get("anti_nuke_enabled",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Role Restore", style=discord.ButtonStyle.success,    row=0)
    async def toggle_restore(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "role_restore_enabled", 0 if s.get("role_restore_enabled",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Link Filter",  style=discord.ButtonStyle.secondary,  row=0)
    async def toggle_links(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "link_filter_enabled", 0 if s.get("link_filter_enabled",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚙️ Advanced Settings",  style=discord.ButtonStyle.blurple,    row=1)
    async def advanced(self, i, b):
        await i.response.send_modal(SecurityModal(self.bot, self.guild))

    @discord.ui.button(label="🔄 Refresh",             style=discord.ButtonStyle.secondary,  row=2)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── Leveling ──────────────────────────────────────────────────────────────────
class LevelingPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        e = comprehensive_embed(title="📊  Leveling & XP", color=0xAA00FF)
        e.add_field(name="Leveling",       value=_on(s.get("leveling_enabled",1)),               inline=True)
        e.add_field(name="Voice XP",       value=_on(s.get("voice_xp_enabled",0)),              inline=True)
        e.add_field(name="Voice Rate",     value=f"{s.get('voice_xp_rate',5)} XP/min",           inline=True)
        e.add_field(name="Level-Up DM",    value=_on(s.get("levelup_dm_enabled",0)),             inline=True)
        e.add_field(name="Level-Up Ch",    value=_ch(s.get("level_up_channel_id")),              inline=True)
        e.add_field(name="Double XP",      value=_on(s.get("double_xp_enabled",0)),              inline=True)
        e.set_footer(text="XERO Dashboard  •  📊 Leveling")
        return e

    @discord.ui.button(label="⚡ Toggle Leveling", style=discord.ButtonStyle.primary,   row=0)
    async def toggle_lv(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "leveling_enabled", 0 if s.get("leveling_enabled",1) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Voice XP", style=discord.ButtonStyle.secondary, row=0)
    async def toggle_vxp(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "voice_xp_enabled", 0 if s.get("voice_xp_enabled",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Double XP",style=discord.ButtonStyle.success,   row=0)
    async def toggle_dxp(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "double_xp_enabled", 0 if s.get("double_xp_enabled",0) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="📢 Set Level-Up Ch", style=discord.ButtonStyle.secondary, row=1)
    async def set_ch(self, i, b):
        await i.response.send_modal(ChannelModal(self.bot, self.guild, [
            ("level_up_channel_id","Level-Up Channel ID","Paste channel ID (blank = where they chatted)"),
        ], title="Level-Up Channel"))

    @discord.ui.button(label="⚙️ DM & Voice Rate",style=discord.ButtonStyle.blurple,   row=1)
    async def advanced(self, i, b):
        await i.response.send_modal(LevelingModal(self.bot, self.guild))

    @discord.ui.button(label="🔄 Refresh",         style=discord.ButtonStyle.secondary, row=2)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── Economy ───────────────────────────────────────────────────────────────────
class EconomyPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT COUNT(*), SUM(wallet+bank), MAX(wallet+bank) FROM economy WHERE guild_id=?",
                                  (self.guild.id,)) as c:
                row = await c.fetchone()
        e = comprehensive_embed(title="💰  Economy", color=0x00E676)
        e.add_field(name="Economy",     value=_on(s.get("economy_enabled",1)),             inline=True)
        e.add_field(name="Active Users",value=str(row[0] or 0),                            inline=True)
        e.add_field(name="Total Wealth",value=f"${int(row[1] or 0):,}",                   inline=True)
        e.add_field(name="Richest",     value=f"${int(row[2] or 0):,}",                   inline=True)
        e.set_footer(text="XERO Dashboard  •  💰 Economy")
        return e

    @discord.ui.button(label="⚡ Toggle Economy",  style=discord.ButtonStyle.primary,   row=0)
    async def toggle_eco(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "economy_enabled", 0 if s.get("economy_enabled",1) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="🔄 Refresh",         style=discord.ButtonStyle.secondary, row=0)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ── AI ─────────────────────────────────────────────────────────────────────────
class AIPanel(SubView):
    PERSONAS = {
        "neutral":"⚖️ Neutral","friendly":"😊 Friendly",
        "analytical":"📊 Analytical","sarcastic":"😏 Sarcastic","mentor":"🧙 Mentor",
    }
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        e = comprehensive_embed(title="🤖  AI & Persona", color=0x00BCD4)
        e.add_field(name="AI Responses",   value=_on(s.get("ai_enabled",1)),                         inline=True)
        e.add_field(name="Persona",        value=self.PERSONAS.get(s.get("persona","neutral"),"⚖️"), inline=True)
        e.add_field(name="Personality",    value=_on(s.get("personality_enabled",1)),                 inline=True)
        e.set_footer(text="XERO Dashboard  •  🤖 AI")
        return e

    @discord.ui.button(label="⚡ Toggle AI",        style=discord.ButtonStyle.primary,   row=0)
    async def toggle_ai(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "ai_enabled", 0 if s.get("ai_enabled",1) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="⚡ Toggle Personality",style=discord.ButtonStyle.secondary, row=0)
    async def toggle_personality(self, i, b):
        s = await _s(self.bot, self.guild.id)
        await _set(self.bot, self.guild.id, "personality_enabled", 0 if s.get("personality_enabled",1) else 1)
        await i.response.edit_message(embed=await self.embed(), view=self)

    @discord.ui.button(label="🎭 Set Persona",       style=discord.ButtonStyle.blurple,   row=0)
    async def set_persona(self, i, b):
        options = [
            discord.SelectOption(label=label, value=key)
            for key, label in self.PERSONAS.items()
        ]
        view = _PersonaSelectView(self.bot, self.guild.id, self)
        await i.response.send_message("Choose AI persona:", view=view)

    @discord.ui.button(label="🔄 Refresh",           style=discord.ButtonStyle.secondary, row=1)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


class _PersonaSelectView(discord.ui.View):
    PERSONAS = {
        "neutral":"⚖️ Neutral","friendly":"😊 Friendly",
        "analytical":"📊 Analytical","sarcastic":"😏 Sarcastic","mentor":"🧙 Mentor",
    }
    def __init__(self, bot, guild_id, parent_view):
        super().__init__(timeout=60)
        self.bot = bot; self.guild_id = guild_id; self.parent = parent_view
        sel = discord.ui.Select(placeholder="Choose persona...", options=[
            discord.SelectOption(label=label, value=key)
            for key, label in self.PERSONAS.items()
        ])
        sel.callback = self._on_select
        self.add_item(sel)
    async def _on_select(self, i):
        persona = i.data["values"][0]
        await _set(self.bot, self.guild_id, "persona", persona)
        label = self.PERSONAS[persona]
        await i.response.send_message(embed=success_embed("Persona Set", f"AI persona → **{label}**"))


# ── Roles ─────────────────────────────────────────────────────────────────────
class RolesPanel(SubView):
    async def embed(self):
        s = await _s(self.bot, self.guild.id)
        e = comprehensive_embed(title="🎭  Roles", color=0x7B2FFF)
        e.add_field(name="Auto-Role",      value=_role(s.get("autorole_id")),             inline=True)
        e.add_field(name="Mute Role",      value=_role(s.get("mute_role_id")),            inline=True)
        e.add_field(name="Verify Role",    value=_role(s.get("verify_role_id")),          inline=True)
        e.add_field(name="Ticket Support", value=_role(s.get("ticket_support_role_id")),  inline=True)
        e.set_footer(text="XERO Dashboard  •  🎭 Roles  •  Paste role IDs")
        return e

    @discord.ui.button(label="⚙️ Set All Roles", style=discord.ButtonStyle.primary,   row=0)
    async def set_roles(self, i, b):
        await i.response.send_message(embed=info_embed(
            "🎭  Set Roles",
            "Use these slash commands — Discord shows a **role picker**, no ID needed:\n\n"
            "**`/config set-autorole @role`** — auto-assign to all new members\n"
            "**`/config set-muterole @role`** — role used for manual mutes\n\n"
            "For verify role: use **`/config dashboard`** → ✅ Verification → Setup\n"
            "For ticket support role: use **`/config dashboard`** → 🎫 Tickets → Setup"
        ))

    @discord.ui.button(label="🔄 Refresh",       style=discord.ButtonStyle.secondary, row=0)
    async def refresh(self, i, b):
        await i.response.edit_message(embed=await self.embed(), view=self)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MASTER DASHBOARD
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class MasterDashboard(discord.ui.View):
    """
    THE config dashboard. One embed, 9 panel buttons.
    Every button opens a sub-panel in the same embed.
    Sub-panels have a ← Back button to return here.
    """
    def __init__(self, bot, guild):
        super().__init__(timeout=300)
        self.bot   = bot
        self.guild = guild

    @staticmethod
    async def build(bot, guild):
        view  = MasterDashboard(bot, guild)
        embed = await view._master_embed(guild)
        return embed, view

    async def _master_embed(self, guild: discord.Guild) -> discord.Embed:
        s = await _s(self.bot, guild.id)
        import os

        def dot(v): return "🟢" if v else "🔴"

        card_set = os.path.exists(f"data/welcome_images/{guild.id}.png")

        e = discord.Embed(
            title=f"⚙️  XERO — Server Dashboard",
            description=(
                f"**{guild.name}** · {guild.member_count:,} members\n"
                "Press a button to open that system's configuration panel.\n"
                "All changes save **instantly**. Back button returns here."
            ),
            color=XERO.PRIMARY
        )
        e.set_thumbnail(url=guild.icon.url if guild.icon else None)
        e.add_field(name="👋 Welcome", value=(
            f"{dot(s.get('welcome_channel_id'))} Channel\n"
            f"{dot(s.get('welcome_dm_enabled',0))} DM on join\n"
            f"{dot(card_set)} Custom card"
        ), inline=True)
        e.add_field(name="📋 Logging", value=(
            f"{dot(s.get('log_channel_id'))} Unified log\n"
            f"{dot(s.get('message_log_channel_id'))} Msg logs\n"
            f"{dot(s.get('webhook_protection_enabled'))} Webhook guard"
        ), inline=True)
        e.add_field(name="✅ Verify  🎫 Tickets", value=(
            f"{dot(s.get('verify_channel_id'))} Verification\n"
            f"{dot(s.get('ticket_support_role_id'))} Tickets"
        ), inline=True)
        e.add_field(name="🛡️ Security", value=(
            f"{dot(s.get('anti_nuke_enabled',0))} Anti-nuke\n"
            f"{dot(s.get('link_filter_enabled',0))} Link filter\n"
            f"{dot(s.get('role_restore_enabled',0))} Role restore"
        ), inline=True)
        e.add_field(name="🤖 AutoMod", value=(
            f"{dot(s.get('automod_enabled',0))} AutoMod\n"
            f"{dot(s.get('automod_anti_spam',0))} Anti-spam\n"
            f"{dot(s.get('automod_anti_links',0))} Link block"
        ), inline=True)
        e.add_field(name="📊 Leveling  💰 Economy", value=(
            f"{dot(s.get('leveling_enabled',1))} Leveling\n"
            f"{dot(s.get('economy_enabled',1))} Economy\n"
            f"{dot(s.get('double_xp_enabled',0))} Double XP"
        ), inline=True)
        e.add_field(name="🤖 AI  🎭 Roles", value=(
            f"{dot(s.get('ai_enabled',1))} AI responses\n"
            f"{dot(s.get('autorole_id'))} Auto-role set\n"
            f"Persona: **{s.get('persona','neutral')}**"
        ), inline=True)
        e.set_footer(text="XERO Config Dashboard  •  🟢 configured  🔴 not set")
        return e

    # Row 0: Core features
    @discord.ui.button(label="👋 Welcome",     style=discord.ButtonStyle.primary,   row=0)
    async def btn_welcome(self, i, b):
        panel = WelcomePanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    @discord.ui.button(label="📋 Logging",     style=discord.ButtonStyle.secondary, row=0)
    async def btn_logging(self, i, b):
        panel = LoggingPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    @discord.ui.button(label="✅ Verification", style=discord.ButtonStyle.success,   row=0)
    async def btn_verify(self, i, b):
        panel = VerificationPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    @discord.ui.button(label="🎫 Tickets",     style=discord.ButtonStyle.blurple,   row=0)
    async def btn_tickets(self, i, b):
        panel = TicketsPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    # Row 1: Moderation
    @discord.ui.button(label="🤖 AutoMod",     style=discord.ButtonStyle.danger,    row=1)
    async def btn_automod(self, i, b):
        panel = AutoModPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    @discord.ui.button(label="🛡️ Security",   style=discord.ButtonStyle.danger,    row=1)
    async def btn_security(self, i, b):
        panel = SecurityPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    @discord.ui.button(label="🎭 Roles",       style=discord.ButtonStyle.secondary, row=1)
    async def btn_roles(self, i, b):
        panel = RolesPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    # Row 2: Engagement
    @discord.ui.button(label="📊 Leveling",    style=discord.ButtonStyle.primary,   row=2)
    async def btn_leveling(self, i, b):
        panel = LevelingPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    @discord.ui.button(label="💰 Economy",     style=discord.ButtonStyle.success,   row=2)
    async def btn_economy(self, i, b):
        panel = EconomyPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    @discord.ui.button(label="🤖 AI",          style=discord.ButtonStyle.blurple,   row=2)
    async def btn_ai(self, i, b):
        panel = AIPanel(self.bot, self.guild)
        await i.response.edit_message(embed=await panel.embed(), view=panel)

    # Row 3: Utility
    @discord.ui.button(label="🔄 Refresh",     style=discord.ButtonStyle.secondary, row=3)
    async def btn_refresh(self, i, b):
        embed = await self._master_embed(i.guild)
        await i.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="🗑️ Reset Server", style=discord.ButtonStyle.danger,   row=3)
    async def btn_reset(self, i, b):
        view = _ConfirmResetView(self.bot, i.guild)
        await i.response.send_message(
            embed=error_embed("⚠️  Reset All Settings?",
                "This will **wipe every XERO setting** for this server.\n"
                "**XP, economy, tickets, and mod cases are NOT affected.**\n\n"
                "You'll need to reconfigure everything from scratch."
            ), view=view, ephemeral=True
        )


class _ConfirmResetView(discord.ui.View):
    def __init__(self, bot, guild):
        super().__init__(timeout=30)
        self.bot = bot; self.guild = guild
    @discord.ui.button(label="Yes, reset everything", style=discord.ButtonStyle.danger)
    async def confirm(self, i, b):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM guild_settings WHERE guild_id=?", (self.guild.id,))
            await db.commit()
        await self.bot.db.create_guild_settings(self.guild.id)
        await i.response.send_message(embed=success_embed("Reset Complete",
            "All settings wiped. Use `/config` to start fresh."))
    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, i, b):
        await i.response.send_message("Cancelled.")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SLASH COMMANDS  (minimal — dashboard does everything)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class Config(commands.GroupCog, name="config"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="dashboard", description="Open the XERO configuration dashboard — configure everything from one place.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def dashboard(self, interaction: discord.Interaction):
        embed, view = await MasterDashboard.build(self.bot, interaction.guild)
        await interaction.response.send_message(embed=embed, view=view)

    @app_commands.command(name="view", description="Quick overview of all current server settings.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def view(self, interaction: discord.Interaction):
        s = await _s(self.bot, interaction.guild.id)
        import os
        def ch(k): return _ch(s.get(k))
        def ro(k): return _role(s.get(k))
        def on(k, d=0): return _on(s.get(k, d))
        e = comprehensive_embed(title=f"⚙️  Full Config — {interaction.guild.name}", color=XERO.PRIMARY, timestamp=discord.utils.utcnow())
        e.add_field(name="📢 Channels", value=(
            f"Welcome: {ch('welcome_channel_id')}\nFarewell: {ch('farewell_channel_id')}\n"
            f"Logs: {ch('log_channel_id')}\nLevel-Up: {ch('level_up_channel_id')}\nBirthday: {ch('birthday_channel_id')}"
        ), inline=True)
        e.add_field(name="🎭 Roles", value=(
            f"Auto: {ro('autorole_id')}\nMute: {ro('mute_role_id')}\n"
            f"Verify: {ro('verify_role_id')}\nTickets: {ro('ticket_support_role_id')}"
        ), inline=True)
        e.add_field(name="🔧 Features", value=(
            f"Leveling: {on('leveling_enabled',1)}\nEconomy: {on('economy_enabled',1)}\n"
            f"AI: {on('ai_enabled',1)}\nAutoMod: {on('automod_enabled',0)}\n"
            f"Anti-Nuke: {on('anti_nuke_enabled',0)}\nDouble XP: {on('double_xp_enabled',0)}"
        ), inline=True)
        e.add_field(name="📋 Logging", value=(
            f"Unified: {ch('log_channel_id')}\nMessages: {ch('message_log_channel_id')}\n"
            f"Members: {ch('member_log_channel_id')}"
        ), inline=True)
        e.add_field(name="🤖 AI", value=f"Persona: **{s.get('persona','neutral')}**", inline=True)
        e.add_field(name="👋 Welcome", value=(
            f"DM: {on('welcome_dm_enabled',0)}\n"
            f"Card: {'✅ Uploaded' if os.path.exists(f'data/welcome_images/{interaction.guild.id}.png') else '❌ None'}"
        ), inline=True)
        e.set_footer(text="Use /config dashboard to change anything")
        await interaction.response.send_message(embed=e)

    @app_commands.command(name="set-farewell", description="Set the farewell channel.")
    @app_commands.describe(channel="Where farewell messages go", message="Custom farewell message (optional)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def set_farewell(self, interaction: discord.Interaction, channel: discord.TextChannel, message: str = None):
        await _set(self.bot, interaction.guild.id, "farewell_channel_id", channel.id)
        if message: await _set(self.bot, interaction.guild.id, "farewell_message", message)
        await interaction.response.send_message(embed=success_embed("Farewell Channel Set", f"Farewell messages will go to {channel.mention}."))

    @app_commands.command(name="set-logs", description="Set logging channels. Pick directly from Discord's channel selector.")
    @app_commands.describe(unified="One channel for ALL events", messages="Message edit/delete logs", members="Join/leave/ban logs", server="Channel/role changes", voice="Voice logs")
    @app_commands.checks.has_permissions(administrator=True)
    async def set_logs(self, interaction: discord.Interaction,
                       unified: discord.TextChannel = None, messages: discord.TextChannel = None,
                       members: discord.TextChannel = None, server: discord.TextChannel = None,
                       voice: discord.TextChannel = None):
        saved = []
        if unified:
            for k in ["log_channel_id","message_log_channel_id","member_log_channel_id","server_log_channel_id","voice_log_channel_id"]:
                await _set(self.bot, interaction.guild.id, k, unified.id)
            saved.append(f"All logs → {unified.mention}")
        if messages: await _set(self.bot, interaction.guild.id, "message_log_channel_id", messages.id); saved.append(f"Messages → {messages.mention}")
        if members:  await _set(self.bot, interaction.guild.id, "member_log_channel_id",  members.id);  saved.append(f"Members → {members.mention}")
        if server:   await _set(self.bot, interaction.guild.id, "server_log_channel_id",  server.id);   saved.append(f"Server → {server.mention}")
        if voice:    await _set(self.bot, interaction.guild.id, "voice_log_channel_id",   voice.id);    saved.append(f"Voice → {voice.mention}")
        adv = self.bot.cogs.get("AdvancedLogger")
        if adv: adv._cache.pop(interaction.guild.id, None)
        await interaction.response.send_message(embed=success_embed("Log Channels Set", "\n".join(saved) or "No changes."))

    @app_commands.command(name="set-autorole", description="Set a role to auto-assign to every new member on join.")
    @app_commands.describe(role="Role to give all new members")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def set_autorole(self, interaction: discord.Interaction, role: discord.Role):
        if role >= interaction.guild.me.top_role:
            return await interaction.response.send_message(embed=error_embed("Role Too High", f"{role.mention} is above my highest role. Move my role above it first."), ephemeral=True)
        await _set(self.bot, interaction.guild.id, "autorole_id", role.id)
        await interaction.response.send_message(embed=success_embed("Auto-Role Set", f"Every new member will receive {role.mention}."))

    @app_commands.command(name="set-muterole", description="Set the mute role for manual mutes.")
    @app_commands.describe(role="The mute role")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def set_muterole(self, interaction: discord.Interaction, role: discord.Role):
        await _set(self.bot, interaction.guild.id, "mute_role_id", role.id)
        await interaction.response.send_message(embed=success_embed("Mute Role Set", f"Mute role → {role.mention}"))

    @app_commands.command(name="set-levelup-channel", description="Set where level-up announcements are posted.")
    @app_commands.describe(channel="Channel for level-up announcements (leave blank = same channel they chatted in)")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def set_levelup_channel(self, interaction: discord.Interaction, channel: discord.TextChannel = None):
        await _set(self.bot, interaction.guild.id, "level_up_channel_id", channel.id if channel else None)
        await interaction.response.send_message(embed=success_embed("Level-Up Channel Set",
            f"Level-ups → {channel.mention if channel else 'same channel they chat in'}"))

    @app_commands.command(name="toggle-leveling", description="Turn XP and leveling on or off.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def toggle_leveling(self, interaction: discord.Interaction):
        s = await _s(self.bot, interaction.guild.id)
        new = 0 if s.get("leveling_enabled", 1) else 1
        await _set(self.bot, interaction.guild.id, "leveling_enabled", new)
        await interaction.response.send_message(embed=success_embed("Leveling " + ("Enabled" if new else "Disabled"), f"XP system is now **{'on' if new else 'off'}**."))

    @app_commands.command(name="toggle-economy", description="Turn the economy system on or off.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def toggle_economy(self, interaction: discord.Interaction):
        s = await _s(self.bot, interaction.guild.id)
        new = 0 if s.get("economy_enabled", 1) else 1
        await _set(self.bot, interaction.guild.id, "economy_enabled", new)
        await interaction.response.send_message(embed=success_embed("Economy " + ("Enabled" if new else "Disabled"), f"Economy is now **{'on' if new else 'off'}**."))

    @app_commands.command(name="toggle-ai", description="Turn AI responses when the bot is @mentioned on or off.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def toggle_ai(self, interaction: discord.Interaction):
        s = await _s(self.bot, interaction.guild.id)
        new = 0 if s.get("ai_enabled", 1) else 1
        await _set(self.bot, interaction.guild.id, "ai_enabled", new)
        await interaction.response.send_message(embed=success_embed("AI Responses " + ("Enabled" if new else "Disabled"), f"AI @mention responses are now **{'on' if new else 'off'}**."))

    @app_commands.command(name="set-persona", description="Set how XERO's AI responds when mentioned.")
    @app_commands.describe(persona="AI personality style")
    @app_commands.choices(persona=[
        app_commands.Choice(name="Neutral — Professional and balanced",     value="neutral"),
        app_commands.Choice(name="Friendly — Warm, casual, uses emojis",    value="friendly"),
        app_commands.Choice(name="Analytical — Highly detailed",             value="analytical"),
        app_commands.Choice(name="Sarcastic — Clever and witty",             value="sarcastic"),
        app_commands.Choice(name="Mentor — Wise and encouraging",            value="mentor"),
    ])
    @app_commands.checks.has_permissions(manage_guild=True)
    async def set_persona(self, interaction: discord.Interaction, persona: str):
        await _set(self.bot, interaction.guild.id, "persona", persona)
        await interaction.response.send_message(embed=success_embed("Persona Set", f"AI personality → **{persona}**"))

    @app_commands.command(name="reset", description="Reset all XERO settings for this server to defaults.")
    @app_commands.checks.has_permissions(administrator=True)
    async def reset(self, interaction: discord.Interaction):
        view = _ConfirmResetView(self.bot, interaction.guild)
        await interaction.response.send_message(embed=error_embed("Reset Everything?", "Wipes all XERO settings for this server. XP, economy, and mod cases are NOT affected."), view=view, ephemeral=True)


    # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    # WELCOME — one command, everything optional, image attachment supported
    # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    @app_commands.command(
        name="welcome",
        description="Set up welcome messages. Attach an image to use as card background."
    )
    @app_commands.describe(
        channel="Channel where welcome messages are posted",
        message="Welcome message text (use {user} {name} {server} {count})",
        image="Background image for welcome cards — bot overlays member name + avatar on it",
        show_name="Show the joining member's name on the card (default: yes)",
        show_avatar="Show their avatar as a circle on the card (default: yes)",
        show_count="Show member count on the card (default: yes)",
        text_position="Where to place the name on the image",
        text_color="Text color as hex (default #FFFFFF)",
        overlay_style="Readability overlay behind the text",
    )
    @app_commands.choices(
        text_position=[
            app_commands.Choice(name="Bottom Left (recommended)", value="bottom_left"),
            app_commands.Choice(name="Bottom Center",             value="bottom_center"),
            app_commands.Choice(name="Bottom Right",              value="bottom_right"),
            app_commands.Choice(name="Center",                    value="center"),
            app_commands.Choice(name="Top Center",                value="top_center"),
        ],
        overlay_style=[
            app_commands.Choice(name="Gradient — dark fade from bottom", value="gradient"),
            app_commands.Choice(name="Solid bar at bottom",               value="bar"),
            app_commands.Choice(name="Full dim overlay",                  value="full"),
            app_commands.Choice(name="None",                              value="none"),
        ]
    )
    @app_commands.checks.has_permissions(manage_guild=True)
    async def welcome(
        self, interaction: discord.Interaction,
        channel: discord.TextChannel,
        message: str = None,
        image: discord.Attachment = None,
        show_name: bool = True,
        show_avatar: bool = True,
        show_count: bool = True,
        text_position: str = "bottom_left",
        text_color: str = "#FFFFFF",
        overlay_style: str = "gradient",
    ):
        await interaction.response.defer(ephemeral=True)

        # Save channel + message
        await _set(self.bot, interaction.guild.id, "welcome_channel_id", channel.id)
        if message:
            await _set(self.bot, interaction.guild.id, "welcome_message", message)

        # Save card settings
        await _set(self.bot, interaction.guild.id, "welcome_card_show_name",   1 if show_name   else 0)
        await _set(self.bot, interaction.guild.id, "welcome_card_show_avatar", 1 if show_avatar else 0)
        await _set(self.bot, interaction.guild.id, "welcome_card_show_count",  1 if show_count  else 0)
        await _set(self.bot, interaction.guild.id, "welcome_card_text_pos",    text_position)
        await _set(self.bot, interaction.guild.id, "welcome_card_text_color",  text_color)
        await _set(self.bot, interaction.guild.id, "welcome_card_overlay",     overlay_style)

        preview_file = None

        # Handle image upload
        if image:
            if not any(image.filename.lower().endswith(e) for e in [".png",".jpg",".jpeg",".gif",".webp"]):
                return await interaction.followup.send(
                    embed=error_embed("Invalid Image", "Attach a PNG, JPG, GIF, or WebP file."),
                    ephemeral=True
                )
            if image.size > 20 * 1024 * 1024:
                return await interaction.followup.send(
                    embed=error_embed("Too Large", "Max 20MB."), ephemeral=True
                )
            import aiohttp as _aio, io as _io
            try:
                async with _aio.ClientSession() as sess:
                    async with sess.get(image.url, timeout=_aio.ClientTimeout(total=15)) as r:
                        img_bytes = await r.read()
                from utils.welcome_card import save_base_image_async
                await save_base_image_async(interaction.guild.id, img_bytes)
                # Clear URL-based fallbacks since file is now primary
                await _set(self.bot, interaction.guild.id, "welcome_image_url",   None)
                await _set(self.bot, interaction.guild.id, "welcome_use_banner",  0)
                await _set(self.bot, interaction.guild.id, "welcome_image_enabled", 0)
            except Exception as e:
                return await interaction.followup.send(
                    embed=error_embed("Image Failed", f"Couldn't process image: {e}"),
                    ephemeral=True
                )

        # Generate live preview
        from utils.welcome_card import generate_welcome_card, fetch_avatar, get_base_image_async
        import io as _io
        _base_img = await get_base_image_async(interaction.guild.id)
        if _base_img:
            av = await fetch_avatar(str(interaction.user.display_avatar.url))
            card = generate_welcome_card(
                guild_id=interaction.guild.id,
                base_bytes=_base_img,
                member_name=interaction.user.display_name,
                member_avatar_bytes=av,
                text_color=text_color, text_position=text_position,
                show_name=show_name, show_avatar=show_avatar, show_member_count=show_count,
                member_count=interaction.guild.member_count,
                server_name=interaction.guild.name, overlay_style=overlay_style,
            )
            if card:
                preview_file = discord.File(_io.BytesIO(card), filename="preview.png")

        # Build response embed
        _tmp_s = await _s(self.bot, interaction.guild.id)
        raw_msg = message or _tmp_s.get("welcome_message") or "Welcome {user} to **{server}**! You are member #{count}."
        preview_msg = raw_msg \
            .replace("{user}", interaction.user.mention) \
            .replace("{name}", interaction.user.display_name) \
            .replace("{server}", interaction.guild.name) \
            .replace("{count}", str(interaction.guild.member_count))

        embed = discord.Embed(
            title="👋  Welcome System Configured",
            color=XERO.SUCCESS,
            timestamp=discord.utils.utcnow()
        )
        embed.add_field(name="📢 Channel",     value=channel.mention, inline=True)
        embed.add_field(name="🖼️ Card Image", value="✅ Uploaded" if _get_base_image(interaction.guild.id) else "❌ None — attach an image to add one", inline=True)
        embed.add_field(name="💬 Message Preview", value=preview_msg[:200], inline=False)
        embed.add_field(
            name="🎨 Card Settings",
            value=(
                f"Name: {'✅' if show_name else '❌'}  "
                f"Avatar: {'✅' if show_avatar else '❌'}  "
                f"Count: {'✅' if show_count else '❌'}\n"
                f"Position: `{text_position}`  Color: `{text_color}`  Overlay: `{overlay_style}`"
            ),
            inline=False
        )
        if preview_file:
            embed.set_image(url="attachment://preview.png")
            embed.set_footer(text="👆 Live preview — this is exactly what new members will see")
        else:
            embed.set_footer(text="Re-run with an image attached to add a welcome card")

        await interaction.followup.send(
            embed=embed,
            file=preview_file if preview_file else discord.utils.MISSING,
            ephemeral=True
        )

    @app_commands.command(
        name="welcome-view",
        description="View the full current welcome setup with a live preview of the card."
    )
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def welcome_view(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        s = await _s(self.bot, interaction.guild.id)
        import os, io as _io
        from utils.welcome_card import generate_welcome_card, fetch_avatar, _get_base_image

        has_card = _get_base_image(interaction.guild.id)
        ch = interaction.guild.get_channel(s.get("welcome_channel_id") or 0)

        embed = comprehensive_embed(title="👋  Welcome Setup", color=XERO.SUCCESS, timestamp=discord.utils.utcnow())
        embed.add_field(name="📢 Channel",     value=ch.mention if ch else "❌ Not set — use `/config welcome #channel`", inline=True)
        embed.add_field(name="📨 DM on Join",  value=_on(s.get("welcome_dm_enabled", 0)), inline=True)
        embed.add_field(name="🖼️ Card Image", value="✅ Uploaded" if has_card else "❌ None", inline=True)
        raw = s.get("welcome_message") or "Welcome {user} to **{server}**! You are member #{count}."
        preview = raw \
            .replace("{user}", interaction.user.mention) \
            .replace("{name}", interaction.user.display_name) \
            .replace("{server}", interaction.guild.name) \
            .replace("{count}", str(interaction.guild.member_count))
        embed.add_field(name="💬 Welcome Message (preview)", value=preview[:300], inline=False)

        if has_card:
            embed.add_field(name="🎨 Card Settings", value=(
                f"Name: {'✅' if s.get('welcome_card_show_name',1) else '❌'}  "
                f"Avatar: {'✅' if s.get('welcome_card_show_avatar',1) else '❌'}  "
                f"Count: {'✅' if s.get('welcome_card_show_count',1) else '❌'}\n"
                f"Position: `{s.get('welcome_card_text_pos','bottom_left')}`  "
                f"Color: `{s.get('welcome_card_text_color','#FFFFFF')}`  "
                f"Overlay: `{s.get('welcome_card_overlay','gradient')}`"
            ), inline=False)
            av   = await fetch_avatar(str(interaction.user.display_avatar.url))
            card = generate_welcome_card(
                guild_id=interaction.guild.id,
                member_name=interaction.user.display_name,
                member_avatar_bytes=av,
                text_color=s.get("welcome_card_text_color","#FFFFFF"),
                text_position=s.get("welcome_card_text_pos","bottom_left"),
                show_name=bool(s.get("welcome_card_show_name",1)),
                show_avatar=bool(s.get("welcome_card_show_avatar",1)),
                show_member_count=bool(s.get("welcome_card_show_count",1)),
                member_count=interaction.guild.member_count,
                server_name=interaction.guild.name,
                overlay_style=s.get("welcome_card_overlay","gradient"),
            )
            if card:
                f = discord.File(_io.BytesIO(card), filename="preview.png")
                embed.set_image(url="attachment://preview.png")
                embed.set_footer(text="👆 Live preview with your name — this is what members see")
                return await interaction.followup.send(embed=embed, file=f)

        embed.set_footer(text="Use /config welcome to change anything")
        await interaction.followup.send(embed=embed)

    @app_commands.command(
        name="welcome-dm",
        description="Configure the DM sent to every member when they join. Attach an image for the DM too."
    )
    @app_commands.describe(
        enabled="Turn welcome DM on or off",
        message="Message members receive in DM (use {user} {name} {server} {count})",
        image="Image to send in the DM (separate from the channel welcome card)",
    )
    @app_commands.checks.has_permissions(manage_guild=True)
    async def welcome_dm(
        self, interaction: discord.Interaction,
        enabled: bool = None,
        message: str = None,
        image: discord.Attachment = None,
    ):
        await interaction.response.defer(ephemeral=True)
        changed = []

        if enabled is not None:
            await _set(self.bot, interaction.guild.id, "welcome_dm_enabled", 1 if enabled else 0)
            changed.append(f"DM {'**enabled** ✅' if enabled else '**disabled** ❌'}")

        if message:
            await _set(self.bot, interaction.guild.id, "welcome_dm_message", message)
            changed.append("DM message saved")

        if image:
            if not any(image.filename.lower().endswith(e) for e in [".png",".jpg",".jpeg",".gif",".webp"]):
                return await interaction.followup.send(embed=error_embed("Invalid Image","PNG/JPG/GIF/WebP only."), ephemeral=True)
            import aiohttp as _aio
            try:
                async with _aio.ClientSession() as sess:
                    async with sess.get(image.url, timeout=_aio.ClientTimeout(total=15)) as r:
                        img_bytes = await r.read()
                # Store DM image separately from channel image
                import os, io as _io
                dm_img_path = f"data/welcome_images/{interaction.guild.id}_dm.png"
                from PIL import Image as _Img
                _img = _Img.open(_io.BytesIO(img_bytes)).convert("RGB")
                _img.save(dm_img_path)
                await _set(self.bot, interaction.guild.id, "welcome_dm_image_url", f"file://{dm_img_path}")
                changed.append("DM image uploaded ✅")
            except Exception as e:
                return await interaction.followup.send(embed=error_embed("Image Failed", str(e)), ephemeral=True)

        s = await _s(self.bot, interaction.guild.id)
        dm_msg = s.get("welcome_dm_message") or "Hey {name}! 👋 Welcome to **{server}**! We're glad to have you."
        preview = dm_msg \
            .replace("{user}", interaction.user.mention) \
            .replace("{name}", interaction.user.display_name) \
            .replace("{server}", interaction.guild.name) \
            .replace("{count}", str(interaction.guild.member_count))

        embed = comprehensive_embed(title="📨  Welcome DM Configured", color=XERO.SUCCESS)
        embed.add_field(name="Status",     value=_on(s.get("welcome_dm_enabled",0)), inline=True)
        embed.add_field(name="DM Image",   value="✅ Custom image set" if s.get("welcome_dm_image_url") else "Uses channel welcome image", inline=True)
        embed.add_field(name="📋 Changes", value="\n".join(changed) or "No changes — specify at least one option.", inline=False)
        embed.add_field(name="💬 DM Preview (what members receive)", value=preview[:400], inline=False)
        embed.set_footer(text="Use /config welcome-dm-view to see full DM preview")
        await interaction.followup.send(embed=embed)

    @app_commands.command(
        name="welcome-dm-view",
        description="Preview exactly what the welcome DM looks like, with image."
    )
    @app_commands.checks.has_permissions(manage_messages=True)
    @command_guard
    async def welcome_dm_view(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        s = await _s(self.bot, interaction.guild.id)

        if not s.get("welcome_dm_enabled", 0):
            return await interaction.followup.send(embed=info_embed(
                "📨  Welcome DM",
                "Welcome DMs are currently **disabled**.\n"
                "Use `/config welcome-dm enabled:True` to turn them on."
            ))

        dm_msg = s.get("welcome_dm_message") or "Hey {name}! 👋 Welcome to **{server}**! We're glad to have you."
        preview = dm_msg \
            .replace("{user}", interaction.user.mention) \
            .replace("{name}", interaction.user.display_name) \
            .replace("{server}", interaction.guild.name) \
            .replace("{count}", str(interaction.guild.member_count))

        # Build what the DM will look like
        dm_embed = discord.Embed(
            title=f"👋  Welcome to {interaction.guild.name}!",
            description=preview,
            color=XERO.PRIMARY
        )
        dm_embed.set_thumbnail(url=interaction.guild.icon.url if interaction.guild.icon else interaction.user.display_avatar.url)
        dm_embed.set_footer(text=f"{interaction.guild.name}  •  Sent by XERO Bot")

        wrapper = discord.Embed(
            title="📨  Welcome DM Preview",
            description="This is exactly what new members receive in their DMs when they join.",
            color=XERO.SECONDARY
        )
        wrapper.set_footer(text="Use /config welcome-dm to change the message or image")

        await interaction.followup.send(embeds=[wrapper, dm_embed])

    @app_commands.command(
        name="welcome-remove",
        description="Remove the welcome card image (keep channel/message settings)."
    )
    @app_commands.checks.has_permissions(manage_guild=True)
    async def welcome_remove(self, interaction: discord.Interaction):
        from utils.welcome_card import delete_base_image
        import os
        delete_base_image(interaction.guild.id)
        # Also remove DM image if it exists
        dm_img = f"data/welcome_images/{interaction.guild.id}_dm.png"
        if os.path.exists(dm_img): os.remove(dm_img)
        await interaction.response.send_message(embed=success_embed(
            "Images Removed",
            "Welcome card images removed.\n"
            "Channel and message settings are still active.\n"
            "Re-run `/config welcome` with an image attached to add a new one."
        ))


    @app_commands.command(name="welcome-image", description="Upload an image to show on welcome cards and DMs.")
    @app_commands.describe(image="PNG or JPG image file to use for welcome messages")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def welcome_image(self, interaction: discord.Interaction, image: discord.Attachment):
        if not image.content_type or not image.content_type.startswith("image/"):
            return await interaction.response.send_message(embed=error_embed("Invalid File", "Please upload a PNG or JPG image."), ephemeral=True)
        await _set(self.bot, interaction.guild.id, "welcome_dm_image_url", image.url)
        e = success_embed("Welcome Image Set", f"Image saved! It will appear on welcome cards and DMs.")
        e.set_image(url=image.url)
        await interaction.response.send_message(embed=e, ephemeral=True)

    @app_commands.command(name="farewell-image", description="Upload an image to show on farewell messages.")
    @app_commands.describe(image="PNG or JPG image file")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def farewell_image(self, interaction: discord.Interaction, image: discord.Attachment):
        if not image.content_type or not image.content_type.startswith("image/"):
            return await interaction.response.send_message(embed=error_embed("Invalid File", "Please upload a PNG or JPG image."), ephemeral=True)
        await _set(self.bot, interaction.guild.id, "farewell_image_url", image.url)
        e = success_embed("Farewell Image Set", "Image saved for farewell messages.")
        e.set_image(url=image.url)
        await interaction.response.send_message(embed=e, ephemeral=True)


async def setup(bot):
    # Add persistent views so verify/ticket buttons survive restarts
    bot.add_view(_VerifyButtonView())
    bot.add_view(_TicketButtonView())
    await bot.add_cog(Config(bot))
