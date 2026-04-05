"""XERO Bot — Role Management (12 commands)"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed

logger = logging.getLogger("XERO.Roles")


class Roles(commands.GroupCog, name="role"):
    def __init__(self, bot):
        self.bot = bot

    def _can_manage_role(self, interaction: discord.Interaction, role: discord.Role) -> bool:
        if role >= interaction.guild.me.top_role:
            return False
        if interaction.user.id != interaction.guild.owner_id and role >= interaction.user.top_role:
            return False
        return True

    @app_commands.command(name="add", description="Give a role to a member.")
    @app_commands.describe(user="Member to give the role to", role="Role to assign")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def add(self, interaction: discord.Interaction, user: discord.Member, role: discord.Role):
        if not self._can_manage_role(interaction, role):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "I can't assign a role higher than my own or yours."), ephemeral=True)
        if role in user.roles:
            return await interaction.response.send_message(embed=error_embed("Already Has Role", f"{user.mention} already has {role.mention}."), ephemeral=True)
        await user.add_roles(role, reason=f"Role added by {interaction.user}")
        await interaction.response.send_message(embed=success_embed("Role Added", f"Gave {role.mention} to {user.mention}."))

    @app_commands.command(name="remove", description="Remove a role from a member.")
    @app_commands.describe(user="Member to remove role from", role="Role to remove")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def remove(self, interaction: discord.Interaction, user: discord.Member, role: discord.Role):
        if not self._can_manage_role(interaction, role):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "I can't remove a role higher than my own or yours."), ephemeral=True)
        if role not in user.roles:
            return await interaction.response.send_message(embed=error_embed("Doesn't Have Role", f"{user.mention} doesn't have {role.mention}."), ephemeral=True)
        await user.remove_roles(role, reason=f"Role removed by {interaction.user}")
        await interaction.response.send_message(embed=success_embed("Role Removed", f"Removed {role.mention} from {user.mention}."))

    @app_commands.command(name="info", description="Get detailed information about a role.")
    @app_commands.describe(role="Role to inspect")
    async def info(self, interaction: discord.Interaction, role: discord.Role):
        perms = [p.replace("_", " ").title() for p, v in role.permissions if v and p not in ("view_channel", "read_message_history")]
        embed = comprehensive_embed(title=f"🎭 {role.name}", color=role.color if role.color.value else discord.Color.blurple())
        embed.add_field(name="🆔 ID", value=f"`{role.id}`", inline=True)
        embed.add_field(name="🎨 Color", value=str(role.color), inline=True)
        embed.add_field(name="📍 Position", value=str(role.position), inline=True)
        embed.add_field(name="👥 Members", value=f"{len(role.members):,}", inline=True)
        embed.add_field(name="👁️ Hoisted", value="Yes" if role.hoist else "No", inline=True)
        embed.add_field(name="📢 Mentionable", value="Yes" if role.mentionable else "No", inline=True)
        embed.add_field(name="📅 Created", value=f"<t:{int(role.created_at.timestamp())}:R>", inline=True)
        embed.add_field(name="🤖 Managed", value="Yes (Bot/Integration)" if role.managed else "No", inline=True)
        if perms:
            embed.add_field(name=f"🔑 Key Permissions ({len(perms)})", value=", ".join(perms[:12]) + ("..." if len(perms) > 12 else ""), inline=False)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="members", description="List all members who have a specific role.")
    @app_commands.describe(role="Role to list members for")
    async def members(self, interaction: discord.Interaction, role: discord.Role):
        members = role.members
        if not members:
            return await interaction.response.send_message(embed=info_embed("No Members", f"No one has {role.mention}."))
        mentions = [m.mention for m in members[:30]]
        embed = comprehensive_embed(
            title=f"👥 Members with {role.name}",
            description=f"**{len(members):,}** member(s)\n\n" + " ".join(mentions) + (f"\n\n*...and {len(members)-30} more*" if len(members) > 30 else ""),
            color=role.color if role.color.value else discord.Color.blurple()
        )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="create", description="Create a new role with custom settings.")
    @app_commands.describe(name="Role name", color="Hex color e.g. #FF5733", hoist="Show separately in member list", mentionable="Allow @mentioning the role")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def create(self, interaction: discord.Interaction, name: str, color: str = None, hoist: bool = False, mentionable: bool = False):
        parsed_color = discord.Color.default()
        if color:
            try:
                parsed_color = discord.Color(int(color.lstrip("#"), 16))
            except ValueError:
                return await interaction.response.send_message(embed=error_embed("Invalid Color", "Use a valid hex color like `#FF5733`."), ephemeral=True)
        role = await interaction.guild.create_role(name=name, color=parsed_color, hoist=hoist, mentionable=mentionable, reason=f"Created by {interaction.user}")
        embed = success_embed("Role Created!", f"{role.mention} has been created.\n**Color:** {parsed_color}\n**Hoisted:** {hoist} | **Mentionable:** {mentionable}")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="delete", description="Delete a role permanently.")
    @app_commands.describe(role="Role to delete", reason="Reason for deletion")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def delete(self, interaction: discord.Interaction, role: discord.Role, reason: str = "No reason provided"):
        if not self._can_manage_role(interaction, role):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "I can't delete a role higher than my own."), ephemeral=True)
        name = role.name
        await role.delete(reason=f"{reason} | By: {interaction.user}")
        await interaction.response.send_message(embed=success_embed("Role Deleted", f"**{name}** has been permanently deleted.\n**Reason:** {reason}"))

    @app_commands.command(name="color", description="Change the color of an existing role.")
    @app_commands.describe(role="Role to recolor", color="New hex color e.g. #FF5733")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def color(self, interaction: discord.Interaction, role: discord.Role, color: str):
        if not self._can_manage_role(interaction, role):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You can't modify this role."), ephemeral=True)
        try:
            new_color = discord.Color(int(color.lstrip("#"), 16))
        except ValueError:
            return await interaction.response.send_message(embed=error_embed("Invalid Color", "Use hex format like `#FF5733`."), ephemeral=True)
        await role.edit(color=new_color, reason=f"Color changed by {interaction.user}")
        await interaction.response.send_message(embed=success_embed("Role Recolored", f"{role.mention} color changed to `{color}`."))

    @app_commands.command(name="rename", description="Rename an existing role.")
    @app_commands.describe(role="Role to rename", new_name="New name for the role")
    @app_commands.checks.has_permissions(manage_roles=True)
    async def rename(self, interaction: discord.Interaction, role: discord.Role, new_name: str):
        if not self._can_manage_role(interaction, role):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "You can't modify this role."), ephemeral=True)
        old_name = role.name
        await role.edit(name=new_name, reason=f"Renamed by {interaction.user}")
        await interaction.response.send_message(embed=success_embed("Role Renamed", f"**{old_name}** → {role.mention}"))

    @app_commands.command(name="all", description="List all roles in this server with member counts.")
    async def all(self, interaction: discord.Interaction):
        roles = sorted(interaction.guild.roles[1:], key=lambda r: r.position, reverse=True)
        lines = [f"{r.mention} — **{len(r.members)}** members" for r in roles[:25]]
        embed = comprehensive_embed(
            title=f"🎭 Server Roles ({len(roles)} total)",
            description="\n".join(lines) + (f"\n*...and {len(roles)-25} more*" if len(roles) > 25 else ""),
            color=discord.Color.blurple()
        )
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="give-all", description="[Admin] Give a role to every member in the server.")
    @app_commands.describe(role="Role to mass-assign")
    @app_commands.checks.has_permissions(administrator=True)
    async def give_all(self, interaction: discord.Interaction, role: discord.Role):
        if not self._can_manage_role(interaction, role):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "I can't assign this role."), ephemeral=True)
        await interaction.response.defer()
        count = 0
        for member in interaction.guild.members:
            if not member.bot and role not in member.roles:
                try:
                    await member.add_roles(role, reason=f"Mass role assign by {interaction.user}")
                    count += 1
                except Exception:
                    pass
        await interaction.followup.send(embed=success_embed("Mass Role Assigned", f"Gave {role.mention} to **{count}** members."))

    @app_commands.command(name="take-all", description="[Admin] Remove a role from every member who has it.")
    @app_commands.describe(role="Role to mass-remove")
    @app_commands.checks.has_permissions(administrator=True)
    async def take_all(self, interaction: discord.Interaction, role: discord.Role):
        if not self._can_manage_role(interaction, role):
            return await interaction.response.send_message(embed=error_embed("Permission Denied", "I can't remove this role."), ephemeral=True)
        await interaction.response.defer()
        count = 0
        for member in role.members:
            try:
                await member.remove_roles(role, reason=f"Mass role removal by {interaction.user}")
                count += 1
            except Exception:
                pass
        await interaction.followup.send(embed=success_embed("Mass Role Removed", f"Removed {role.mention} from **{count}** members."))

    @app_commands.command(name="bots", description="View all bot roles and managed integrations.")
    async def bots(self, interaction: discord.Interaction):
        bot_roles = [r for r in interaction.guild.roles if r.managed]
        if not bot_roles:
            return await interaction.response.send_message(embed=info_embed("No Bot Roles", "No managed/bot roles found."))
        embed = comprehensive_embed(title="🤖 Bot/Integration Roles", color=discord.Color.blurple())
        for r in bot_roles:
            embed.add_field(name=r.name, value=f"ID: `{r.id}` | Members: {len(r.members)}", inline=True)
        await interaction.response.send_message(embed=embed)


async def setup(bot):
    await bot.add_cog(Roles(bot))
