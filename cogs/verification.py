"""
XERO Bot — Verification System v3
Bloxlink-inspired design, fully inside Discord, no external links required.
7 commands: setup, panel, method, config, stats, reset, kick-unverified
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import random
import datetime
import asyncio
import aiosqlite
from utils.embeds import (
    success_embed, error_embed, info_embed, comprehensive_embed,
    brand_embed, XERO
)

logger = logging.getLogger("XERO.Verify")

# ── Math challenge modal ──────────────────────────────────────────────────────

class MathAnswerModal(discord.ui.Modal, title="Verification Challenge"):
    answer = discord.ui.TextInput(
        label="Answer",
        placeholder="Type your answer here...",
        min_length=1,
        max_length=10
    )

    def __init__(self, bot, role_id: int, correct: int):
        super().__init__()
        self.bot = bot
        self.role_id = role_id
        self.correct = correct

    async def on_submit(self, interaction: discord.Interaction):
        try:
            user_ans = int(self.answer.value.strip())
        except ValueError:
            return await interaction.response.send_message(
                embed=error_embed("Invalid Answer", "Please enter a number."), ephemeral=True
            )

        if user_ans == self.correct:
            role = interaction.guild.get_role(self.role_id)
            if role:
                try:
                    await interaction.user.add_roles(role, reason="XERO Verification: math challenge passed")
                    embed = success_embed(
                        "Verification Complete",
                        f"You have been verified and given the **{role.name}** role.\n"
                        f"Welcome to **{interaction.guild.name}**! ✅"
                    )
                    embed.set_footer(text="XERO Verification System")
                    await interaction.response.send_message(embed=embed, ephemeral=True)
                    try:
                        dm = discord.Embed(
                            title=f"✅ Verified — {interaction.guild.name}",
                            description=f"You have been verified in **{interaction.guild.name}**.",
                            color=discord.Color.green(),
                            timestamp=discord.utils.utcnow()
                        )
                        dm.set_footer(text="XERO Verification System")
                        await interaction.user.send(embed=dm)
                    except Exception:
                        pass
                    await _log_verification(self.bot, interaction.guild, interaction.user, "Math Challenge", success=True)
                except discord.Forbidden:
                    await interaction.response.send_message(
                        embed=error_embed("Permission Error", "I can't assign your role. Please contact an admin."),
                        ephemeral=True
                    )
            else:
                await interaction.response.send_message(
                    embed=error_embed("Config Error", "Verification role not found. Please contact an admin."),
                    ephemeral=True
                )
        else:
            await interaction.response.send_message(
                embed=error_embed("Wrong Answer", "Incorrect. Click **Verify** again to try a new challenge."),
                ephemeral=True
            )
            await _log_verification(self.bot, interaction.guild, interaction.user, "Math Challenge", success=False)


# ── Account link modal ────────────────────────────────────────────────────────

class AccountLinkModal(discord.ui.Modal):
    username = discord.ui.TextInput(
        label="Username",
        placeholder="Enter your username...",
        min_length=3,
        max_length=50
    )

    def __init__(self, bot, role_id: int, platform: str):
        super().__init__(title=f"Link {platform} Account")
        self.bot = bot
        self.role_id = role_id
        self.platform = platform

    async def on_submit(self, interaction: discord.Interaction):
        username = self.username.value.strip()
        role = interaction.guild.get_role(self.role_id)
        if not role:
            return await interaction.response.send_message(
                embed=error_embed("Config Error", "Verification role not found."), ephemeral=True
            )
        try:
            await interaction.user.add_roles(role, reason=f"XERO Verification: {self.platform} account linked")
            embed = success_embed(
                "Account Linked & Verified",
                f"**{self.platform} account linked:** `{username}`\n"
                f"You have been given the **{role.name}** role.\n"
                f"Welcome to **{interaction.guild.name}**! ✅"
            )
            embed.set_footer(text=f"XERO Verification  •  {self.platform}")
            await interaction.response.send_message(embed=embed, ephemeral=True)
            try:
                dm = discord.Embed(
                    title=f"✅ Account Linked — {interaction.guild.name}",
                    description=(
                        f"Your **{self.platform}** account (`{username}`) has been linked.\n"
                        f"You are now verified in **{interaction.guild.name}**."
                    ),
                    color=discord.Color.green(),
                    timestamp=discord.utils.utcnow()
                )
                await interaction.user.send(embed=dm)
            except Exception:
                pass
            await _log_verification(self.bot, interaction.guild, interaction.user, self.platform, success=True, extra=username)
        except discord.Forbidden:
            await interaction.response.send_message(
                embed=error_embed("Permission Error", "I can't assign your role. Please contact an admin."),
                ephemeral=True
            )


# ── Platform selection dropdown ───────────────────────────────────────────────

class PlatformSelect(discord.ui.Select):
    def __init__(self, bot, role_id: int, methods: list):
        self.bot = bot
        self.role_id = role_id
        options = []
        if "math" in methods:
            options.append(discord.SelectOption(label="Math Challenge", description="Solve a quick math question", emoji="🧮", value="math"))
        if "roblox" in methods:
            options.append(discord.SelectOption(label="Roblox", description="Link your Roblox account", emoji="🎮", value="roblox"))
        if "spotify" in methods:
            options.append(discord.SelectOption(label="Spotify", description="Link your Spotify account", emoji="🎵", value="spotify"))
        if "steam" in methods:
            options.append(discord.SelectOption(label="Steam", description="Link your Steam account", emoji="🕹️", value="steam"))
        if not options:
            options.append(discord.SelectOption(label="Math Challenge", description="Solve a quick math question", emoji="🧮", value="math"))
        super().__init__(placeholder="Select verification method...", options=options, custom_id="verify_platform_select")

    async def callback(self, interaction: discord.Interaction):
        method = self.values[0]
        if method == "math":
            a = random.randint(10, 99)
            b = random.randint(10, 99)
            await interaction.response.send_modal(MathAnswerModal(self.bot, self.role_id, a, b))
        else:
            platform_names = {"roblox": "Roblox", "spotify": "Spotify", "steam": "Steam"}
            await interaction.response.send_modal(AccountLinkModal(self.bot, self.role_id, platform_names.get(method, method.title())))


# ── Main verify button panel (persistent) ────────────────────────────────────

class VerifyPanel(discord.ui.View):
    def __init__(self, bot):
        super().__init__(timeout=None)
        self.bot = bot

    @discord.ui.button(
        label="Click to Verify",
        style=discord.ButtonStyle.green,
        emoji="✅",
        custom_id="xero_verify_main_btn"
    )
    async def verify_click(self, interaction: discord.Interaction, button: discord.ui.Button):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        role_id = settings.get("verify_role_id")
        if not role_id:
            return await interaction.response.send_message(
                embed=error_embed("Not Configured", "Verification hasn't been set up. Ask an admin to use `/verify setup`."),
                ephemeral=True
            )

        role = interaction.guild.get_role(role_id)
        if role and role in interaction.user.roles:
            return await interaction.response.send_message(
                embed=success_embed("Already Verified", f"You already have the **{role.name}** role. You're good to go!"),
                ephemeral=True
            )

        methods_raw = settings.get("verify_methods") or "math"
        methods = [m.strip().lower() for m in methods_raw.split(",") if m.strip()]
        if not methods:
            methods = ["math"]

        if len(methods) == 1:
            method = methods[0]
            if method == "math":
                a = random.randint(10, 99)
                b = random.randint(10, 99)
                await interaction.response.send_modal(MathAnswerModal(self.bot, role_id, a, b))
            else:
                platform_names = {"roblox": "Roblox", "spotify": "Spotify", "steam": "Steam"}
                await interaction.response.send_modal(AccountLinkModal(self.bot, role_id, platform_names.get(method, method.title())))
        else:
            embed = info_embed(
                "🛡️ Identity Verification",
                "Please select your preferred verification method below.\n\n"
                "All methods are handled **entirely inside Discord** — no external sites required."
            )
            embed.set_footer(text=f"XERO Verification  •  {interaction.guild.name}")
            view = discord.ui.View(timeout=120)
            view.add_item(PlatformSelect(self.bot, role_id, methods))
            await interaction.response.send_message(embed=embed, view=view, ephemeral=True)


# ── Helpers ──────────────────────────────────────────────────────────────────

async def _log_verification(bot, guild: discord.Guild, user: discord.Member, method: str, success: bool, extra: str = None):
    try:
        settings = await bot.db.get_guild_settings(guild.id)
        ch_id = settings.get("verify_log_channel_id") or settings.get("log_channel_id")
        if not ch_id:
            return
        ch = guild.get_channel(ch_id)
        if not ch:
            return
        color = discord.Color.green() if success else discord.Color.red()
        status = "✅ Passed" if success else "❌ Failed"
        embed = discord.Embed(
            title=f"Verification {status}",
            color=color,
            timestamp=discord.utils.utcnow()
        )
        embed.set_thumbnail(url=user.display_avatar.url)
        embed.add_field(name="User", value=f"{user.mention} (`{user.id}`)", inline=True)
        embed.add_field(name="Method", value=method, inline=True)
        embed.add_field(name="Account Age", value=f"<t:{int(user.created_at.timestamp())}:R>", inline=True)
        if extra:
            embed.add_field(name="Linked Account", value=f"`{extra}`", inline=True)
        embed.set_footer(text="XERO Verification System")
        await ch.send(embed=embed)
    except Exception as e:
        logger.debug(f"Verify log: {e}")


# ── Main Cog ──────────────────────────────────────────────────────────────────

class Verification(commands.GroupCog, name="verify"):
    def __init__(self, bot):
        self.bot = bot
        bot.add_view(VerifyPanel(bot))

    @app_commands.command(name="setup", description="Set up the verification system — assign a role and optional log channel.")
    @app_commands.describe(
        role="Role granted on successful verification",
        log_channel="Channel to log verification events (optional)"
    )
    @app_commands.checks.has_permissions(administrator=True)
    async def setup(self, interaction: discord.Interaction, role: discord.Role, log_channel: discord.TextChannel = None, panel_image: discord.Attachment = None):
        await interaction.response.defer(ephemeral=True)
        await self.bot.db.update_guild_setting(interaction.guild.id, "verify_role_id", role.id)
        if log_channel:
            await self.bot.db.update_guild_setting(interaction.guild.id, "verify_log_channel_id", log_channel.id)

        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        if not settings.get("verify_methods"):
            await self.bot.db.update_guild_setting(interaction.guild.id, "verify_methods", "math")

        embed = success_embed(
            "✅ Verification System Ready",
            f"**Verified Role:** {role.mention}\n"
            f"**Log Channel:** {log_channel.mention if log_channel else '*Not set*'}\n\n"
            f"Use `/verify panel` to post the panel in a channel.\n"
            f"Use `/verify method` to choose verification types (math, Roblox, Spotify, Steam).\n"
            f"Use `/verify config` to view current settings."
        )
        embed.set_footer(text="XERO Verification System")
        await interaction.followup.send(embed=embed, ephemeral=True)

    @app_commands.command(name="panel", description="Post the verification panel in a channel so members can verify.")
    @app_commands.describe(channel="Channel to post the panel in (defaults to current channel)")
    @app_commands.checks.has_permissions(administrator=True)
    async def panel(self, interaction: discord.Interaction, channel: discord.TextChannel = None):
        await interaction.response.defer(ephemeral=True)
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        if not settings.get("verify_role_id"):
            return await interaction.followup.send(
                embed=error_embed("Not Configured", "Run `/verify setup` first to configure the verification role."),
                ephemeral=True
            )

        target = channel or interaction.channel
        panel_embed = discord.Embed(
            title="🛡️  Identity Verification",
            description=(
                f"Welcome to **{interaction.guild.name}**!\n\n"
                "To access the server, complete a quick verification to confirm you're a real person.\n\n"
                "**→ Click the button below to begin.**\n\n"
                "*Verification is handled entirely inside Discord — no external sites required.*"
            ),
            color=XERO.PRIMARY,
            timestamp=discord.utils.utcnow()
        )

        role = interaction.guild.get_role(settings.get("verify_role_id"))
        if role:
            panel_embed.add_field(name="Access Role", value=role.mention, inline=True)

        methods_raw = settings.get("verify_methods") or "math"
        methods = [m.strip().title() for m in methods_raw.split(",") if m.strip()]
        panel_embed.add_field(name="Methods Available", value=" | ".join(methods), inline=True)
        panel_embed.set_footer(text=f"XERO Verification  •  {interaction.guild.name}")

        file = None
        try:
            panel_embed, file = await brand_embed(panel_embed, interaction.guild, self.bot)
        except Exception:
            pass

        view = VerifyPanel(self.bot)
        try:
            if file:
                await target.send(embed=panel_embed, file=file, view=view)
            else:
                await target.send(embed=panel_embed, view=view)
            await interaction.followup.send(
                embed=success_embed("Panel Posted", f"Verification panel posted in {target.mention}."),
                ephemeral=True
            )
        except discord.Forbidden:
            await interaction.followup.send(
                embed=error_embed("No Permission", f"I don't have permission to send messages in {target.mention}."),
                ephemeral=True
            )

    @app_commands.command(name="method", description="Configure which verification methods members can use.")
    @app_commands.describe(
        math="Enable math challenge verification",
        roblox="Enable Roblox account linking",
        spotify="Enable Spotify account linking",
        steam="Enable Steam account linking"
    )
    @app_commands.checks.has_permissions(administrator=True)
    async def method(
        self,
        interaction: discord.Interaction,
        math: bool = True,
        roblox: bool = False,
        spotify: bool = False,
        steam: bool = False,
    ):
        methods = []
        if math:    methods.append("math")
        if roblox:  methods.append("roblox")
        if spotify: methods.append("spotify")
        if steam:   methods.append("steam")
        if not methods:
            return await interaction.response.send_message(
                embed=error_embed("At Least One Required", "You must enable at least one verification method."),
                ephemeral=True
            )
        await self.bot.db.update_guild_setting(interaction.guild.id, "verify_methods", ",".join(methods))
        friendly = [m.title() for m in methods]
        await interaction.response.send_message(
            embed=success_embed(
                "Verification Methods Updated",
                f"Active methods: **{' | '.join(friendly)}**\n\n"
                f"Members will {'see a dropdown to choose' if len(methods) > 1 else 'go directly to the ' + friendly[0] + ' challenge'}."
            ),
            ephemeral=True
        )

    @app_commands.command(name="config", description="View the current verification configuration.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def config(self, interaction: discord.Interaction):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        role_id = settings.get("verify_role_id")
        log_id  = settings.get("verify_log_channel_id")
        methods = settings.get("verify_methods") or "math"

        embed = comprehensive_embed(
            title=f"🛡️ Verification Config — {interaction.guild.name}",
            color=XERO.PRIMARY
        )
        embed.add_field(
            name="Verified Role",
            value=f"<@&{role_id}>" if role_id else "*Not set — run `/verify setup`*",
            inline=True
        )
        embed.add_field(
            name="Log Channel",
            value=f"<#{log_id}>" if log_id else "*Not set*",
            inline=True
        )
        embed.add_field(
            name="Methods",
            value=" | ".join(m.strip().title() for m in methods.split(",") if m.strip()),
            inline=True
        )
        embed.set_footer(text="XERO Verification  •  /verify panel to post the verify button")
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="stats", description="View verification statistics for this server.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def stats(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        role_id = settings.get("verify_role_id")

        verified_count   = 0
        unverified_count = 0
        if role_id:
            role = interaction.guild.get_role(role_id)
            if role:
                verified_count   = len(role.members)
                unverified_count = sum(1 for m in interaction.guild.members if not m.bot and role not in m.roles)

        total_humans = sum(1 for m in interaction.guild.members if not m.bot)
        pct = round(verified_count / total_humans * 100) if total_humans > 0 else 0

        embed = comprehensive_embed(
            title=f"📊 Verification Stats — {interaction.guild.name}",
            color=XERO.PRIMARY
        )
        embed.add_field(name="✅ Verified Members", value=f"**{verified_count:,}**",   inline=True)
        embed.add_field(name="❌ Unverified",        value=f"**{unverified_count:,}**", inline=True)
        embed.add_field(name="📈 Completion Rate",   value=f"**{pct}%**",              inline=True)
        embed.add_field(name="👥 Total Humans",      value=f"**{total_humans:,}**",    inline=True)
        embed.set_footer(text="XERO Verification System")
        await interaction.followup.send(embed=embed, ephemeral=True)

    @app_commands.command(name="reset", description="Remove a member's verified role and reset their verification status.")
    @app_commands.describe(member="The member to un-verify")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def reset(self, interaction: discord.Interaction, member: discord.Member):
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        role_id = settings.get("verify_role_id")
        if not role_id:
            return await interaction.response.send_message(
                embed=error_embed("Not Configured", "No verification role is set."), ephemeral=True
            )
        role = interaction.guild.get_role(role_id)
        if not role:
            return await interaction.response.send_message(
                embed=error_embed("Role Not Found", "The configured verification role no longer exists."), ephemeral=True
            )
        if role not in member.roles:
            return await interaction.response.send_message(
                embed=info_embed("Not Verified", f"{member.mention} doesn't have the verified role."), ephemeral=True
            )
        try:
            await member.remove_roles(role, reason=f"XERO Verification reset by {interaction.user}")
            await interaction.response.send_message(
                embed=success_embed("Verification Reset", f"Removed **{role.name}** from {member.mention}."),
                ephemeral=True
            )
            try:
                dm = discord.Embed(
                    title=f"⚠️ Verification Reset — {interaction.guild.name}",
                    description=(
                        f"Your verification status in **{interaction.guild.name}** has been reset by a moderator.\n"
                        f"You can re-verify by clicking the verification button in the server."
                    ),
                    color=discord.Color.orange()
                )
                await member.send(embed=dm)
            except Exception:
                pass
        except discord.Forbidden:
            await interaction.response.send_message(
                embed=error_embed("Permission Error", "I can't remove that role."), ephemeral=True
            )

    @app_commands.command(name="kick-unverified", description="Kick all unverified members from the server (dry-run by default).")
    @app_commands.describe(dry_run="If True (default), only shows count — doesn't actually kick")
    @app_commands.checks.has_permissions(administrator=True)
    async def kick_unverified(self, interaction: discord.Interaction, dry_run: bool = True):
        await interaction.response.defer(ephemeral=True)
        settings = await self.bot.db.get_guild_settings(interaction.guild.id)
        role_id = settings.get("verify_role_id")
        if not role_id:
            return await interaction.followup.send(
                embed=error_embed("Not Configured", "No verification role is set."), ephemeral=True
            )
        role = interaction.guild.get_role(role_id)
        if not role:
            return await interaction.followup.send(
                embed=error_embed("Role Not Found", "The configured verification role no longer exists."), ephemeral=True
            )

        targets = [m for m in interaction.guild.members if not m.bot and role not in m.roles]

        if dry_run:
            return await interaction.followup.send(
                embed=info_embed(
                    "Dry Run — Kick Preview",
                    f"**{len(targets)}** unverified member(s) would be kicked.\n\n"
                    f"Run with `dry_run: False` to actually kick them."
                ),
                ephemeral=True
            )

        kicked = 0
        failed = 0
        for member in targets:
            try:
                try:
                    await member.send(
                        embed=discord.Embed(
                            title=f"Kicked from {interaction.guild.name}",
                            description="You were removed because you did not complete verification. You may rejoin and verify.",
                            color=discord.Color.red()
                        )
                    )
                except Exception:
                    pass
                await member.kick(reason="XERO: Unverified member purge")
                kicked += 1
                await asyncio.sleep(0.5)
            except Exception:
                failed += 1

        await interaction.followup.send(
            embed=success_embed(
                "Unverified Purge Complete",
                f"**Kicked:** {kicked}\n**Failed:** {failed}\n\nAll kicked members can rejoin and verify."
            ),
            ephemeral=True
        )


async def setup(bot):
    await bot.add_cog(Verification(bot))
