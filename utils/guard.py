import asyncio, discord, functools, logging
_glog = logging.getLogger("XERO.Guard")

def command_guard(func):
    """Wraps any slash command to guarantee a response even if it crashes."""
    @functools.wraps(func)
    async def wrapper(self, interaction: discord.Interaction, *args, **kwargs):
        try:
            # External APIs (AI/vision/transcription) can legitimately take longer than
            # the default interaction expectations, especially during provider load.
            # Keep a guard timeout, but make it less aggressive to avoid false failures.
            await asyncio.wait_for(func(self, interaction, *args, **kwargs), timeout=60.0)
        except asyncio.TimeoutError:
            _glog.warning(f"Command {func.__name__} timed out")
            try:
                e = discord.Embed(title="Timed out", description="This took too long. Please try again.", color=0xFF1744)
                if interaction.response.is_done():
                    await interaction.followup.send(embed=e, ephemeral=True)
                else:
                    await interaction.response.send_message(embed=e, ephemeral=True)
            except Exception: pass
        except Exception as ex:
            _glog.error(f"Command {func.__name__} crashed: {ex}", exc_info=True)
            try:
                e = discord.Embed(title="Something went wrong", description="An error occurred. Please try again.", color=0xFF1744)
                if interaction.response.is_done():
                    await interaction.followup.send(embed=e, ephemeral=True)
                else:
                    await interaction.response.send_message(embed=e, ephemeral=True)
            except Exception: pass
    return wrapper
