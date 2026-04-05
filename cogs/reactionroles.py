"""XERO Bot — Reaction Roles (Persistent Button Panels) — 6 commands"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import aiosqlite
import json
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.ReactionRoles")


class RoleButton(discord.ui.Button):
    def __init__(self, role_id: int, label: str, emoji: str = None, style: discord.ButtonStyle = discord.ButtonStyle.blurple):
        super().__init__(label=label, emoji=emoji, style=style, custom_id=f"rrole_{role_id}")
        self.role_id = role_id

    async def callback(self, interaction: discord.Interaction):
        role = interaction.guild.get_role(self.role_id)
        if not role:
            return await interaction.response.send_message("⚠️ Role not found. Please contact an admin.", ephemeral=True)
        if role in interaction.user.roles:
            await interaction.user.remove_roles(role, reason="Reaction role toggle")
            await interaction.response.send_message(f"✅ Removed {role.mention} from you.")
        else:
            await interaction.user.add_roles(role, reason="Reaction role toggle")
            await interaction.response.send_message(f"✅ Gave you {role.mention}!")


class RolePanelView(discord.ui.View):
    def __init__(self, roles_data: list):
        super().__init__(timeout=None)
        for item in roles_data:
            style_map = {
                "blurple": discord.ButtonStyle.blurple,
                "green": discord.ButtonStyle.green,
                "red": discord.ButtonStyle.danger,
                "grey": discord.ButtonStyle.secondary
            }
            style = style_map.get(item.get("style", "blurple"), discord.ButtonStyle.blurple)
            self.add_item(RoleButton(
                role_id=item["role_id"],
                label=item["label"],
                emoji=item.get("emoji"),
                style=style
            ))


class ReactionRoles(commands.GroupCog, name="reactionroles"):
    def __init__(self, bot):
        self.bot = bot
        bot.loop.create_task(self._restore_panels())

    async def _restore_panels(self):
        await self.bot.wait_until_ready()
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute("SELECT * FROM reaction_role_panels") as c:
                    panels = [dict(r) for r in await c.fetchall()]
            for panel in panels:
                roles_data = json.loads(panel["roles_data"])
                view = RolePanelView(roles_data)
                self.bot.add_view(view)
            logger.info(f"✓ Restored {len(panels)} reaction role panels")
        except Exception as e:
            logger.error(f"Panel restore error: {e}")

    @app_commands.command(name="create-panel", description="Create a button-based role selection panel.")
    @app_commands.describe(title="Panel title", description="Panel description", channel="Channel to post the panel")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def create_panel(self, interaction: discord.Interaction, title: str, description: str = "Click a button to get or remove a role!", channel: discord.TextChannel = None):
        ch = channel or interaction.channel
        # Store in DB as pending (no roles yet)
        async with self.bot.db._db_context() as db:
            async with db.execute(
                "INSERT INTO reaction_role_panels (guild_id, channel_id, title, description, roles_data) VALUES (?,?,?,?,?)",
                (interaction.guild.id, ch.id, title, description, json.dumps([]))
            ) as c:
                panel_id = c.lastrowid
            await db.commit()
        await interaction.response.send_message(
            embed=success_embed("Panel Created!", f"Panel **#{panel_id}** created.\n\nNow add roles with:\n`/reactionroles add-role panel_id:{panel_id} role:@Role label:Click Me`\n\nThen publish it with:\n`/reactionroles publish panel_id:{panel_id}`"),
            ephemeral=True
        )

    @app_commands.command(name="add-role", description="Add a role button to an existing panel.")
    @app_commands.describe(panel_id="Panel ID", role="Role to assign", label="Button label", emoji="Button emoji", style="Button color")
    @app_commands.choices(style=[
        app_commands.Choice(name="Blue", value="blurple"),
        app_commands.Choice(name="Green", value="green"),
        app_commands.Choice(name="Red", value="red"),
        app_commands.Choice(name="Grey", value="grey"),
    ])
    @app_commands.checks.has_permissions(manage_roles=True)
    async def add_role(self, interaction: discord.Interaction, panel_id: int, role: discord.Role, label: str, emoji: str = None, style: str = "blurple"):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM reaction_role_panels WHERE id=? AND guild_id=?", (panel_id, interaction.guild.id)) as c:
                panel = await c.fetchone()
        if not panel:
            return await interaction.response.send_message(embed=error_embed("Not Found", f"Panel #{panel_id} not found."), ephemeral=True)
        panel = dict(panel)
        roles_data = json.loads(panel["roles_data"])
        if len(roles_data) >= 25:
            return await interaction.response.send_message(embed=error_embed("Panel Full", "Maximum 25 role buttons per panel."), ephemeral=True)
        roles_data.append({"role_id": role.id, "label": label, "emoji": emoji, "style": style})
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE reaction_role_panels SET roles_data=? WHERE id=?", (json.dumps(roles_data), panel_id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Role Added!", f"{role.mention} added to panel **#{panel_id}** with label **{label}**."))

    @app_commands.command(name="publish", description="Publish a reaction roles panel to its channel.")
    @app_commands.describe(panel_id="Panel ID to publish")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def publish(self, interaction: discord.Interaction, panel_id: int):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM reaction_role_panels WHERE id=? AND guild_id=?", (panel_id, interaction.guild.id)) as c:
                panel = await c.fetchone()
        if not panel:
            return await interaction.response.send_message(embed=error_embed("Not Found", f"Panel #{panel_id} not found."), ephemeral=True)
        panel = dict(panel)
        roles_data = json.loads(panel["roles_data"])
        if not roles_data:
            return await interaction.response.send_message(embed=error_embed("No Roles", "Add roles first with `/reactionroles add-role`."), ephemeral=True)
        ch = interaction.guild.get_channel(panel["channel_id"]) or interaction.channel
        from utils.embeds import brand_embed, comprehensive_embed
        embed = comprehensive_embed(title=panel["title"], description=panel["description"], color=discord.Color.blurple())
        embed.set_footer(text="Click a button to get/remove the role")
        role_list = []
        for r in roles_data:
            role = interaction.guild.get_role(r["role_id"])
            if role:
                role_list.append(f"{r.get('emoji', '•')} {role.mention} — {r['label']}")
        embed.add_field(name="Available Roles", value="\n".join(role_list) if role_list else "None", inline=False)
        
        # Unified Branding
        embed, file = await brand_embed(embed, interaction.guild, self.bot)
        view = RolePanelView(roles_data)
        if file:
            msg = await ch.send(embed=embed, view=view, file=file)
        else:
            msg = await ch.send(embed=embed, view=view)
        async with self.bot.db._db_context() as db:
            await db.execute("UPDATE reaction_role_panels SET message_id=? WHERE id=?", (msg.id, panel_id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Panel Published!", f"Reaction roles panel **#{panel_id}** is now live in {ch.mention}!"))

    @app_commands.command(name="list-panels", description="View all reaction role panels in this server.")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def list_panels(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute("SELECT * FROM reaction_role_panels WHERE guild_id=?", (interaction.guild.id,)) as c:
                panels = [dict(r) for r in await c.fetchall()]
        if not panels:
            return await interaction.response.send_message(embed=info_embed("No Panels", "No reaction role panels found. Create one with `/reactionroles create-panel`."))
        embed = comprehensive_embed(title="🎭 Reaction Role Panels", description=f"**{len(panels)}** panel(s)", color=discord.Color.blurple())
        for p in panels:
            roles_data = json.loads(p["roles_data"])
            ch = interaction.guild.get_channel(p["channel_id"])
            embed.add_field(
                name=f"#{p['id']} — {p['title']}",
                value=f"**Channel:** {ch.mention if ch else 'Unknown'}\n**Roles:** {len(roles_data)}\n**Published:** {'Yes ✅' if p.get('message_id') else 'No ❌'}",
                inline=True
            )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="delete-panel", description="[Admin] Delete a reaction roles panel.")
    @app_commands.describe(panel_id="Panel ID to delete")
    @app_commands.checks.has_permissions(administrator=True)
    async def delete_panel(self, interaction: discord.Interaction, panel_id: int):
        async with self.bot.db._db_context() as db:
            async with db.execute("SELECT channel_id, message_id FROM reaction_role_panels WHERE id=? AND guild_id=?", (panel_id, interaction.guild.id)) as c:
                panel = await c.fetchone()
        if panel:
            ch = interaction.guild.get_channel(panel[0])
            if ch and panel[1]:
                try:
                    msg = await ch.fetch_message(panel[1])
                    await msg.delete()
                except Exception:
                    pass
        async with self.bot.db._db_context() as db:
            await db.execute("DELETE FROM reaction_role_panels WHERE id=? AND guild_id=?", (panel_id, interaction.guild.id))
            await db.commit()
        await interaction.response.send_message(embed=success_embed("Panel Deleted", f"Reaction roles panel **#{panel_id}** has been deleted."))


async def setup(bot):
    await bot.add_cog(ReactionRoles(bot))
