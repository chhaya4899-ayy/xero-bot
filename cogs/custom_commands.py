"""XERO Bot — Custom Commands System (6 commands)
Admins create their own slash-style commands with text/embed responses.
Members trigger them with /cmd <name>.
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import aiosqlite
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.CustomCommands")

COLOR_MAP = {
    "blue": discord.Color.blue(), "red": discord.Color.red(),
    "green": discord.Color.green(), "gold": discord.Color.gold(),
    "purple": discord.Color.purple(), "orange": discord.Color.orange(),
    "teal": discord.Color.teal(), "pink": discord.Color.pink(),
}


class CustomCommands(commands.GroupCog, name="cmd"):
    def __init__(self, bot):
        self.bot = bot

    # ── Create ────────────────────────────────────────────────────────────
    @app_commands.command(name="create", description="[Admin] Create a custom command for this server.")
    @app_commands.describe(
        name="Command trigger name (e.g. 'rules', 'socials', 'staff')",
        response="Response text. Use {user} for mentioning the caller.",
        embed_title="Optional: make it an embed with this title",
        embed_color="Embed color",
        role="Optional: grant/remove this role when triggered",
    )
    @app_commands.choices(embed_color=[
        app_commands.Choice(name="Blue", value="blue"),
        app_commands.Choice(name="Green", value="green"),
        app_commands.Choice(name="Red", value="red"),
        app_commands.Choice(name="Gold", value="gold"),
        app_commands.Choice(name="Purple", value="purple"),
        app_commands.Choice(name="Orange", value="orange"),
    ])
    @app_commands.checks.has_permissions(manage_guild=True)
    async def create(self, interaction: discord.Interaction, name: str, response: str,
                     embed_title: str = None, embed_color: str = "blue", role: discord.Role = None):
        name = name.lower().strip().replace(" ", "-")
        if len(name) > 32:
            return await interaction.response.send_message(
                embed=error_embed("Name Too Long", "Command name must be 32 characters or less."), ephemeral=True)
        async with self.bot.db._db_context() as db:
            try:
                await db.execute(
                    "INSERT INTO custom_commands (guild_id, name, response, embed_title, embed_color, role_id, created_by) VALUES (?,?,?,?,?,?,?)",
                    (interaction.guild.id, name, response, embed_title, embed_color, role.id if role else None, interaction.user.id)
                )
                await db.commit()
            except Exception:
                return await interaction.response.send_message(
                    embed=error_embed("Already Exists", f"A command named `{name}` already exists. Use `/cmd edit` to modify it."),
                    ephemeral=True)
        embed = success_embed("Custom Command Created!", (
            f"**Trigger:** `/cmd use name:{name}`\n"
            f"**Response:** {response[:200]}\n"
            f"**Embed:** {'Yes — ' + embed_title if embed_title else 'No (plain text)'}\n"
            f"**Role Action:** {role.mention if role else 'None'}"
        ))
        await interaction.response.send_message(embed=embed)

    # ── Use ───────────────────────────────────────────────────────────────
    @app_commands.command(name="use", description="Use a custom command created for this server.")
    @app_commands.describe(name="Name of the custom command to trigger")
    async def use(self, interaction: discord.Interaction, name: str):
        name = name.lower().strip()
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM custom_commands WHERE guild_id=? AND name=?",
                (interaction.guild.id, name)
            ) as c:
                cmd = await c.fetchone()
        if not cmd:
            # Suggest close matches
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute("SELECT name FROM custom_commands WHERE guild_id=?", (interaction.guild.id,)) as c:
                    all_cmds = [r["name"] for r in await c.fetchall()]
            suggestions = [c for c in all_cmds if name[:3] in c or c[:3] in name]
            hint = f"\n\nDid you mean: {', '.join(f'`{s}`' for s in suggestions[:3])}?" if suggestions else ""
            return await interaction.response.send_message(
                embed=error_embed("Command Not Found", f"No command named `{name}` exists.{hint}"), ephemeral=True)
        cmd = dict(cmd)
        response_text = cmd["response"].replace("{user}", interaction.user.mention)
        if cmd.get("embed_title"):
            color = COLOR_MAP.get(cmd.get("embed_color", "blue"), discord.Color.blue())
            embed = comprehensive_embed(title=cmd["embed_title"], description=response_text, color=color)
            embed.set_footer(text=f"Custom Command: {name} | XERO Bot")
            await interaction.response.send_message(embed=embed)
        else:
            await interaction.response.send_message(response_text)
        # Handle role toggle
        if cmd.get("role_id"):
            role = interaction.guild.get_role(cmd["role_id"])
            if role:
                try:
                    if role in interaction.user.roles:
                        await interaction.user.remove_roles(role, reason=f"Custom command /{name}")
                    else:
                        await interaction.user.add_roles(role, reason=f"Custom command /{name}")
                except Exception:
                    pass
        # Increment uses
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE custom_commands SET uses=uses+1 WHERE guild_id=? AND name=?",
                             (interaction.guild.id, name))
            await db.commit()

    # ── Edit ──────────────────────────────────────────────────────────────
    @app_commands.command(name="edit", description="[Admin] Edit an existing custom command's response.")
    @app_commands.describe(name="Command to edit", new_response="New response text", new_embed_title="New embed title")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def edit(self, interaction: discord.Interaction, name: str, new_response: str, new_embed_title: str = None):
        name = name.lower().strip()
        async with self.bot.db._db_context() as db:
            if new_embed_title is not None:
                await db.execute(
                    "UPDATE custom_commands SET response=?, embed_title=? WHERE guild_id=? AND name=?",
                    (new_response, new_embed_title, interaction.guild.id, name)
                )
            else:
                await db.execute(
                    "UPDATE custom_commands SET response=? WHERE guild_id=? AND name=?",
                    (new_response, interaction.guild.id, name)
                )
            if db.total_changes == 0:
                return await interaction.response.send_message(
                    embed=error_embed("Not Found", f"No command named `{name}`."), ephemeral=True)
            await db.commit()
        await interaction.response.send_message(
            embed=success_embed("Command Updated", f"Custom command `{name}` has been updated."))

    # ── Delete ────────────────────────────────────────────────────────────
    @app_commands.command(name="delete", description="[Admin] Delete a custom command.")
    @app_commands.describe(name="Command to delete")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def delete(self, interaction: discord.Interaction, name: str):
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM custom_commands WHERE guild_id=? AND name=?",
                             (interaction.guild.id, name.lower()))
            await db.commit()
        await interaction.response.send_message(
            embed=success_embed("Deleted", f"Custom command `{name}` has been removed."))

    # ── List ──────────────────────────────────────────────────────────────
    @app_commands.command(name="list", description="View all custom commands for this server.")
    async def list_cmds(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT name, uses, embed_title, role_id FROM custom_commands WHERE guild_id=? ORDER BY uses DESC",
                (interaction.guild.id,)
            ) as c:
                cmds = [dict(r) for r in await c.fetchall()]
        if not cmds:
            return await interaction.response.send_message(embed=info_embed(
                "No Custom Commands",
                "No custom commands yet. Admins can create them with `/cmd create`."))
        embed = comprehensive_embed(
            title=f"⚡ Custom Commands ({len(cmds)})",
            description="Use `/cmd use name:<command>` to trigger any of these.",
            color=discord.Color.blurple()
        )
        for cmd in cmds[:20]:
            role = interaction.guild.get_role(cmd["role_id"]) if cmd.get("role_id") else None
            extras = []
            if cmd.get("embed_title"):
                extras.append("📋 Embed")
            if role:
                extras.append(f"🎭 {role.name}")
            embed.add_field(
                name=f"`{cmd['name']}`",
                value=f"**Used:** {cmd['uses']:,}x{(' | ' + ' | '.join(extras)) if extras else ''}",
                inline=True
            )
        await interaction.response.send_message(embed=embed)

    # ── Info ──────────────────────────────────────────────────────────────
    @app_commands.command(name="info", description="Get detailed info about a specific custom command.")
    @app_commands.describe(name="Command to inspect")
    async def info(self, interaction: discord.Interaction, name: str):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM custom_commands WHERE guild_id=? AND name=?",
                (interaction.guild.id, name.lower())
            ) as c:
                cmd = await c.fetchone()
        if not cmd:
            return await interaction.response.send_message(
                embed=error_embed("Not Found", f"No command named `{name}`."), ephemeral=True)
        cmd = dict(cmd)
        creator = interaction.guild.get_member(cmd.get("created_by"))
        role = interaction.guild.get_role(cmd.get("role_id")) if cmd.get("role_id") else None
        embed = info_embed(f"Command: {cmd['name']}", "")
        embed.add_field(name="Response Preview", value=cmd["response"][:300], inline=False)
        embed.add_field(name="Type", value="Embed" if cmd.get("embed_title") else "Plain Text", inline=True)
        embed.add_field(name="Uses", value=f"{cmd['uses']:,}", inline=True)
        embed.add_field(name="Role Action", value=role.mention if role else "None", inline=True)
        embed.add_field(name="Created By", value=creator.mention if creator else "Unknown", inline=True)
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(CustomCommands(bot))
