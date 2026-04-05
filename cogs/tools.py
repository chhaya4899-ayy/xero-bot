"""XERO Bot — /tools group (calc, timestamp, weather, define, color, emojis, snipe)"""
import discord
from discord.ext import commands
from discord import app_commands
import logging, datetime, math, urllib.parse, aiohttp
from utils.embeds import success_embed, error_embed, info_embed, XERO, comprehensive_embed

logger = logging.getLogger("XERO.Tools")
SNIPE_CACHE: dict = {}


class Tools(commands.GroupCog, name="tools"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="calc", description="Evaluate math — sqrt, sin, cos, log, pi, e, powers, trig.")
    @app_commands.describe(expression="e.g. sqrt(144), 2**10, sin(pi/2), log(100)")
    async def calc(self, interaction: discord.Interaction, expression: str):
        try:
            safe = expression.replace("^","**").replace("×","*").replace("÷","/")
            fns  = {k:v for k,v in vars(math).items() if not k.startswith("_")}
            fns.update({"abs":abs,"round":round,"min":min,"max":max,"int":int,"float":float})
            result = eval(safe, {"__builtins__":{}}, fns)
            if isinstance(result,float) and result==int(result): result=int(result)
            await interaction.response.send_message(embed=success_embed("🧮 Calculator",f"**Input:** `{expression}`\n**Result:** `{result}`"))
        except ZeroDivisionError:
            await interaction.response.send_message(embed=error_embed("Division by Zero","Can't divide by zero."),ephemeral=True)
        except Exception:
            await interaction.response.send_message(embed=error_embed("Invalid Expression",f"Could not evaluate `{expression}`.\nTip: use `sqrt()`, `**` for power, `sin()`, `log()`."),ephemeral=True)

    @app_commands.command(name="timestamp", description="Convert any date/time to Discord timestamp codes for every format.")
    @app_commands.describe(year="Year",month="Month 1-12",day="Day 1-31",hour="Hour 0-23 UTC",minute="Minute 0-59")
    async def timestamp(self, interaction: discord.Interaction, year: int, month: int, day: int, hour: int=0, minute: int=0):
        try:
            dt = datetime.datetime(year,month,day,hour,minute,tzinfo=datetime.timezone.utc)
            ts = int(dt.timestamp())
            embed = info_embed("🕐 Timestamp Generator",f"**Date:** {dt.strftime('%B %d, %Y at %H:%M UTC')}\n**Unix:** `{ts}`")
            for name,fmt in [("Short Time","t"),("Long Time","T"),("Short Date","d"),("Long Date","D"),("Date+Time","f"),("Full","F"),("Relative","R")]:
                embed.add_field(name=name,value=f"<t:{ts}:{fmt}>\n`<t:{ts}:{fmt}>`",inline=True)
            await interaction.response.send_message(embed=embed)
        except ValueError as e:
            await interaction.response.send_message(embed=error_embed("Invalid Date",str(e)),ephemeral=True)

    @app_commands.command(name="weather", description="Real-time weather for any city — temp, wind, humidity, UV, 3-day forecast.")
    @app_commands.describe(city="City name e.g. New York, Tokyo, London")
    async def weather(self, interaction: discord.Interaction, city: str):
        await interaction.response.defer()
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get(f"https://wttr.in/{urllib.parse.quote(city)}?format=j1",timeout=aiohttp.ClientTimeout(total=10)) as r:
                    if r.status!=200: return await interaction.followup.send(embed=error_embed("Not Found",f"No weather data for **{city}**."))
                    data=await r.json()
            c=data["current_condition"][0]; area=data["nearest_area"][0]
            desc=c["weatherDesc"][0]["value"]; dl=desc.lower()
            emo="⛈️" if "thunder" in dl else "🌧️" if "rain" in dl else "🌨️" if "snow" in dl else "🌫️" if "fog" in dl else "☁️" if "cloud" in dl else "⛅" if "partly" in dl else "☀️"
            embed=comprehensive_embed(title=f"{emo} {area['areaName'][0]['value']}, {area['country'][0]['value']}",description=f"**{desc}**",color=XERO.INFO)
            embed.add_field(name="🌡️ Temp",      value=f"**{c['temp_C']}°C** / {c['temp_F']}°F\nFeels: {c['FeelsLikeC']}°C",inline=True)
            embed.add_field(name="💧 Humidity",  value=f"**{c['humidity']}%**",inline=True)
            embed.add_field(name="💨 Wind",       value=f"**{c['windspeedKmph']} km/h {c['winddir16Point']}**",inline=True)
            embed.add_field(name="👁️ Visibility",value=f"**{c['visibility']} km**",inline=True)
            embed.add_field(name="☀️ UV Index",  value=f"**{c.get('uvIndex','N/A')}**",inline=True)
            embed.add_field(name="☁️ Cloud",     value=f"**{c['cloudcover']}%**",inline=True)
            forecast=""
            for day in data.get("weather",[])[:3]:
                dd=day["hourly"][4]["weatherDesc"][0]["value"] if day.get("hourly") else ""
                forecast+=f"**{day['date']}:** {day['maxtempC']}°/{day['mintempC']}°C — {dd}\n"
            if forecast: embed.add_field(name="📅 3-Day Forecast",value=forecast,inline=False)
            embed.set_footer(text="Powered by wttr.in • XERO Bot")
            await interaction.followup.send(embed=embed)
        except Exception as e:
            logger.error(f"Weather: {e}")
            await interaction.followup.send(embed=error_embed("Error",f"Could not fetch weather for **{city}**."))

    @app_commands.command(name="define", description="Look up any English word — definition, examples, synonyms, antonyms, phonetics.")
    @app_commands.describe(word="Word to define")
    async def define(self, interaction: discord.Interaction, word: str):
        await interaction.response.defer()
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get(f"https://api.dictionaryapi.dev/api/v2/entries/en/{urllib.parse.quote(word.lower())}",timeout=aiohttp.ClientTimeout(total=10)) as r:
                    if r.status!=200: return await interaction.followup.send(embed=error_embed("Not Found",f"No definition for **{word}**."))
                    data=await r.json()
            entry=data[0]; phonetic=entry.get("phonetic","")
            audio=next((p.get("audio") for p in entry.get("phonetics",[]) if p.get("audio")),None)
            embed=comprehensive_embed(title=f"📖 {word.capitalize()}",description=f"Phonetic: **{phonetic}**" if phonetic else None,color=XERO.INFO)
            for meaning in entry.get("meanings",[])[:3]:
                pos=meaning["partOfSpeech"]; defs=meaning.get("definitions",[])[:2]
                syns=meaning.get("synonyms",[])[:4]; ants=meaning.get("antonyms",[])[:2]
                for i,d in enumerate(defs):
                    val=f"**{d.get('definition','')}**"
                    if d.get("example"): val+=f'\n*"{d["example"]}"*'
                    if i==0 and syns: val+=f"\n**Synonyms:** {', '.join(syns)}"
                    if i==0 and ants: val+=f"\n**Antonyms:** {', '.join(ants)}"
                    embed.add_field(name=f"*{pos}*",value=val[:600],inline=False)
            if audio: embed.add_field(name="🔊 Pronunciation",value=f"[Listen]({audio})",inline=True)
            embed.set_footer(text="Free Dictionary API • XERO Bot")
            await interaction.followup.send(embed=embed)
        except Exception as e:
            logger.error(f"Define: {e}")
            await interaction.followup.send(embed=error_embed("Error",f"Could not define **{word}**."))

    @app_commands.command(name="color", description="Preview a hex color — RGB, HSL, decimal, complementary, brightness analysis.")
    @app_commands.describe(hex_code="Hex color e.g. FF5733 or #1A2B3C")
    async def color(self, interaction: discord.Interaction, hex_code: str):
        try:
            clean=hex_code.lstrip("#").upper()
            if len(clean)!=6: raise ValueError
            r,g,b=int(clean[0:2],16),int(clean[2:4],16),int(clean[4:6],16)
            r_,g_,b_=r/255,g/255,b/255
            cmax,cmin=max(r_,g_,b_),min(r_,g_,b_); delta=cmax-cmin
            l=(cmax+cmin)/2; s=0.0 if delta==0 else delta/(1-abs(2*l-1))
            h=0
            if delta!=0:
                if cmax==r_: h=60*(((g_-b_)/delta)%6)
                elif cmax==g_: h=60*((b_-r_)/delta+2)
                else: h=60*((r_-g_)/delta+4)
            comp=f"{255-r:02X}{255-g:02X}{255-b:02X}"
            embed=comprehensive_embed(title=f"🎨 Color: #{clean}",color=discord.Color(int(clean,16)))
            embed.add_field(name="HEX",value=f"`#{clean}`",inline=True)
            embed.add_field(name="RGB",value=f"`rgb({r},{g},{b})`",inline=True)
            embed.add_field(name="HSL",value=f"`hsl({int(h)}°,{int(s*100)}%,{int(l*100)}%)`",inline=True)
            embed.add_field(name="Decimal",value=f"`{int(clean,16)}`",inline=True)
            embed.add_field(name="Complement",value=f"`#{comp}`",inline=True)
            embed.add_field(name="Brightness",value="Light ☀️" if l>0.5 else "Dark 🌑",inline=True)
            embed.set_image(url=f"https://singlecolorimage.com/get/{clean}/300x80")
            await interaction.response.send_message(embed=embed)
        except Exception:
            await interaction.response.send_message(embed=error_embed("Invalid","Use 6-char hex like `FF5733`."),ephemeral=True)

    @app_commands.command(name="emojis", description="Browse all custom emojis — static and animated — with usage syntax.")
    async def emojis(self, interaction: discord.Interaction):
        if not interaction.guild.emojis: return await interaction.response.send_message(embed=info_embed("No Custom Emojis","This server has no custom emojis."))
        static=[e for e in interaction.guild.emojis if not e.animated]; animated=[e for e in interaction.guild.emojis if e.animated]
        embed=comprehensive_embed(title=f"😄 Custom Emojis — {interaction.guild.name}",description=f"**{len(interaction.guild.emojis)}** total • {len(static)} static • {len(animated)} animated",color=XERO.PRIMARY)
        if static: embed.add_field(name=f"Static ({len(static)})",value=" ".join(str(e) for e in static[:30])[:1024],inline=False)
        if animated: embed.add_field(name=f"Animated ({len(animated)})",value=" ".join(str(e) for e in animated[:30])[:1024],inline=False)
        embed.add_field(name="💡 Tip",value="Use `/info emoji <name>` for full details on any emoji.",inline=False)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="snipe", description="Retrieve the most recently deleted message in this channel.")
    async def snipe(self, interaction: discord.Interaction):
        cached=SNIPE_CACHE.get(interaction.channel.id)
        if not cached: return await interaction.response.send_message(embed=info_embed("Nothing to Snipe","No recently deleted messages here."),ephemeral=True)
        embed=comprehensive_embed(title="🔫 Sniped Message",description=cached["content"][:2000] or "*[No text content]*",color=XERO.WARNING)
        embed.set_author(name=cached["author"],icon_url=cached.get("avatar") or discord.Embed.Empty)
        embed.set_footer(text=f"Deleted at {cached['timestamp'].strftime('%H:%M:%S, %B %d %Y')}")
        if cached.get("image"): embed.set_image(url=cached["image"])
        await interaction.response.send_message(embed=embed)

    @commands.Cog.listener()
    async def on_message_delete(self, message: discord.Message):
        if message.author.bot or not message.guild: return
        img=next((a.url for a in message.attachments if a.filename.lower().endswith((".png",".jpg",".jpeg",".gif",".webp"))),None) if message.attachments else None
        SNIPE_CACHE[message.channel.id]={"content":message.content,"author":str(message.author),"avatar":str(message.author.display_avatar.url),"timestamp":datetime.datetime.now(),"image":img}


async def setup(bot):
    await bot.add_cog(Tools(bot))
