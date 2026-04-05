"""XERO Bot — Social with real GIFs + 12 actions"""
import discord
from utils.guard import command_guard
from discord.ext import commands
from discord import app_commands
import logging, random, aiohttp
from utils.embeds import XERO, comprehensive_embed

logger = logging.getLogger("XERO.Social")

ACTION_DATA = {
    "hug":{"emoji":"🤗","color":0xFF69B4,"lines":["hugged","gave the warmest hug to","wrapped arms around","squeezed tight"]},
    "kiss":{"emoji":"💋","color":0xFF1493,"lines":["kissed","gave a sweet kiss to","planted one on"]},
    "pat":{"emoji":"🥺","color":0xFFB6C1,"lines":["patted","gave headpats to","gently patted"]},
    "slap":{"emoji":"👋","color":0xFF6347,"lines":["slapped","gave a big slap to","whacked"]},
    "cuddle":{"emoji":"🥰","color":0xFFB6C1,"lines":["is cuddling with","snuggled up with","is cozy with"]},
    "dance":{"emoji":"💃","color":0xDA70D6,"lines":["is dancing with","twirled with","busted a move with"]},
    "highfive":{"emoji":"🙌","color":0x00FF94,"lines":["high-fived","celebrated with","slapped hands with"]},
    "wave":{"emoji":"👋","color":0x87CEEB,"lines":["waved at","said hi to","greeted"]},
    "bite":{"emoji":"😬","color":0xFF4500,"lines":["bit","took a nibble from","chomped on"]},
    "poke":{"emoji":"👉","color":0xFFD700,"lines":["poked","jabbed","nudged"]},
    "stare":{"emoji":"👀","color":0x9370DB,"lines":["is staring at","can't stop staring at","is eyeing"]},
    "shoot":{"emoji":"🔫","color":0x808080,"lines":["pointed finger-guns at","went pew pew at"]},
}

async def fetch_gif(action: str):
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(f"https://nekos.best/api/v2/{action}",timeout=aiohttp.ClientTimeout(total=6)) as r:
                if r.status==200:
                    data=await r.json()
                    results=data.get("results",[])
                    if results: return results[0].get("url")
    except Exception: pass
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(f"https://api.otakugifs.xyz/gif?reaction={action}&format=gif",timeout=aiohttp.ClientTimeout(total=6)) as r:
                if r.status==200:
                    data=await r.json()
                    u=data.get("url")
                    if u: return u
    except Exception: pass
    return None

class Social(commands.GroupCog, name="social"):
    def __init__(self, bot): self.bot = bot

    @command_guard
    async def _act(self, interaction, action, user):
        if user==interaction.user: return await interaction.response.send_message(f"You can't {action} yourself!",ephemeral=True)
        await interaction.response.defer()
        info=ACTION_DATA.get(action,{"emoji":"✨","color":0x7B2FFF,"lines":["did something to"]})
        verb=random.choice(info["lines"])
        embed=comprehensive_embed(description=f"{interaction.user.mention} **{verb}** {user.mention}! {info['emoji']}",color=discord.Color(info["color"]))
        gif=await fetch_gif(action)
        if gif: embed.set_image(url=gif)
        embed.set_footer(text="XERO Social • nekos.best")
        await interaction.followup.send(embed=embed)

    @app_commands.command(name="hug",description="Give someone a warm hug! 🤗")
    @app_commands.describe(user="Who to hug")
    async def hug(self,i,user:discord.Member): await self._act(i,"hug",user)
    @app_commands.command(name="kiss",description="Give someone a kiss! 💋")
    @app_commands.describe(user="Who to kiss")
    async def kiss(self,i,user:discord.Member): await self._act(i,"kiss",user)
    @app_commands.command(name="pat",description="Give someone headpats! 🥺")
    @app_commands.describe(user="Who to pat")
    async def pat(self,i,user:discord.Member): await self._act(i,"pat",user)
    @app_commands.command(name="slap",description="Slap someone playfully! 👋")
    @app_commands.describe(user="Who to slap")
    async def slap(self,i,user:discord.Member): await self._act(i,"slap",user)
    @app_commands.command(name="cuddle",description="Cuddle with someone! 🥰")
    @app_commands.describe(user="Who to cuddle")
    async def cuddle(self,i,user:discord.Member): await self._act(i,"cuddle",user)
    @app_commands.command(name="dance",description="Dance with someone! 💃")
    @app_commands.describe(user="Who to dance with")
    async def dance(self,i,user:discord.Member): await self._act(i,"dance",user)
    @app_commands.command(name="highfive",description="High five! 🙌")
    @app_commands.describe(user="Who to high five")
    async def highfive(self,i,user:discord.Member): await self._act(i,"highfive",user)
    @app_commands.command(name="wave",description="Wave at someone! 👋")
    @app_commands.describe(user="Who to wave at")
    async def wave(self,i,user:discord.Member): await self._act(i,"wave",user)
    @app_commands.command(name="bite",description="Bite someone! 😬")
    @app_commands.describe(user="Who to bite")
    async def bite(self,i,user:discord.Member): await self._act(i,"bite",user)
    @app_commands.command(name="poke",description="Poke someone! 👉")
    @app_commands.describe(user="Who to poke")
    async def poke(self,i,user:discord.Member): await self._act(i,"poke",user)
    @app_commands.command(name="stare",description="Intensely stare at someone... 👀")
    @app_commands.describe(user="Who to stare at")
    async def stare(self,i,user:discord.Member): await self._act(i,"stare",user)
    @app_commands.command(name="shoot",description="Finger guns! 🔫")
    @app_commands.describe(user="Who to shoot")
    async def shoot(self,i,user:discord.Member): await self._act(i,"shoot",user)

async def setup(bot):
    await bot.add_cog(Social(bot))
