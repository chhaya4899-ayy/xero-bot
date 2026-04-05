"""XERO Bot — Music Player (12 commands)
Optimized for Railway: Uses SoundCloud as primary search to bypass YouTube bot-blocking.
No external API keys required.
Commands: play, stop, skip, queue, pause, resume, volume, nowplaying, loop, shuffle, remove, clear
"""
import discord
from discord.ext import commands
from discord import app_commands
import logging
import asyncio
import random as _random
import aiohttp
import urllib.parse
from utils.embeds import success_embed, error_embed, info_embed, comprehensive_embed
from utils.guard import command_guard

logger = logging.getLogger("XERO.Music")

try:
    import yt_dlp
    YTDLP_AVAILABLE = True
except ImportError:
    YTDLP_AVAILABLE = False
    logger.warning("yt-dlp not installed.")

SEARCH_OPTS = {
    "format": "bestaudio/best",
    "noplaylist": True,
    "quiet": True,
    "no_warnings": True,
    "default_search": "scsearch",
    "nocheckcertificate": True,
    "ignoreerrors": True,
}

EXTRACT_OPTS = {
    "format": "bestaudio/best",
    "noplaylist": True,
    "quiet": True,
    "no_warnings": True,
    "nocheckcertificate": True,
    "ignoreerrors": True,
    "source_address": "0.0.0.0",
}

FFMPEG_OPTS = {
    "before_options": "-reconnect 1 -reconnect_streamed 1 -reconnect_delay_max 5 -nostdin",
    "options": "-vn",
}


class MusicQueue:
    def __init__(self):
        self.songs: list[dict] = []
        self.volume: float = 0.5
        self.loop: bool = False
        self.shuffle: bool = False
        self.now_playing: dict | None = None


def _fmt_duration(seconds: int) -> str:
    if not seconds:
        return "Live"
    m, s = divmod(int(seconds), 60)
    h, m = divmod(m, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def _search_sync(query: str) -> dict:
    is_url = query.startswith(("http://", "https://", "www."))
    
    # Use different options for search vs extraction
    opts = EXTRACT_OPTS if is_url else SEARCH_OPTS
    search_query = query if is_url else f"scsearch:{query}"
    
    with yt_dlp.YoutubeDL(opts) as ydl:
        try:
            info = ydl.extract_info(search_query, download=False)
        except Exception as e:
            logger.error(f"yt-dlp error: {e}")
            raise ValueError(f"Extraction failed: {e}")

        if not info:
            raise ValueError(f"No results found for: {query}")

        # If it's a playlist/search result, take the first entry
        if "entries" in info:
            if not info["entries"]:
                raise ValueError(f"No entries found for: {query}")
            info = info["entries"][0]

        # Ensure we have a playable URL
        url = info.get("url")
        if not url:
            raise ValueError("No playable URL found in metadata.")

        return {
            "url": url,
            "title": info.get("title", "Unknown"),
            "duration": info.get("duration", 0),
            "thumbnail": info.get("thumbnail"),
            "webpage_url": info.get("webpage_url", query if is_url else ""),
            "uploader": info.get("uploader", "Unknown"),
        }


class Music(commands.GroupCog, name="music"):
    def __init__(self, bot: commands.Bot):
        self.bot = bot
        self.queues: dict[int, MusicQueue] = {}

    def get_queue(self, guild_id: int) -> MusicQueue:
        if guild_id not in self.queues:
            self.queues[guild_id] = MusicQueue()
        return self.queues[guild_id]

    def _play_next(self, guild_id: int) -> None:
        queue = self.get_queue(guild_id)
        guild = self.bot.get_guild(guild_id)
        if not guild or not guild.voice_client:
            return
        vc = guild.voice_client
        if vc.is_playing() or vc.is_paused():
            return
        if queue.loop and queue.now_playing:
            queue.songs.insert(0, queue.now_playing)
        if not queue.songs:
            queue.now_playing = None
            return
        if queue.shuffle and len(queue.songs) > 1:
            idx = _random.randint(0, len(queue.songs) - 1)
            queue.songs[0], queue.songs[idx] = queue.songs[idx], queue.songs[0]
        song = queue.songs.pop(0)
        queue.now_playing = song
        try:
            source = discord.FFmpegPCMAudio(song["url"], **FFMPEG_OPTS)
            source = discord.PCMVolumeTransformer(source, volume=queue.volume)
            vc.play(
                source,
                after=lambda e: asyncio.run_coroutine_threadsafe(
                    self._after_song(guild_id, e), self.bot.loop
                ),
            )
        except Exception as e:
            logger.error(f"[Music] Playback error: {e}")
            self._play_next(guild_id)

    async def _after_song(self, guild_id: int, error=None) -> None:
        if error:
            logger.error(f"[Music] After-song error: {error}")
        self._play_next(guild_id)

    async def _ensure_voice(self, interaction: discord.Interaction) -> bool:
        if not interaction.user.voice or not interaction.user.voice.channel:
            await interaction.response.send_message(
                embed=error_embed("No Voice", "Join a voice channel first."), ephemeral=True
            )
            return False
        return True

    # ── 1. Play ───────────────────────────────────────────────────────────────

    @app_commands.command(name="play", description="Play a song — searches SoundCloud by default.")
    @app_commands.describe(query="Song name or URL (YouTube / SoundCloud)")
    @command_guard
    async def play(self, interaction: discord.Interaction, query: str):
        if not await self._ensure_voice(interaction):
            return
        if not YTDLP_AVAILABLE:
            return await interaction.response.send_message(
                embed=error_embed("Missing Dependency", "yt-dlp is not installed."), ephemeral=True
            )
        await interaction.response.defer()
        try:
            loop = asyncio.get_event_loop()
            song = await asyncio.wait_for(
                loop.run_in_executor(None, _search_sync, query), timeout=30.0
            )
        except asyncio.TimeoutError:
            return await interaction.followup.send(
                embed=error_embed("Timeout", "Search took too long. Try again.")
            )
        except Exception as e:
            return await interaction.followup.send(
                embed=error_embed("Not Found", f"Could not find: `{query}`")
            )
        vc = interaction.guild.voice_client
        if not vc:
            try:
                vc = await interaction.user.voice.channel.connect(timeout=10.0, reconnect=True)
            except Exception as e:
                return await interaction.followup.send(
                    embed=error_embed("Voice Error", f"Failed to connect: {e}")
                )
        queue = self.get_queue(interaction.guild.id)
        if vc.is_playing() or vc.is_paused():
            queue.songs.append(song)
            embed = info_embed(
                "Added to Queue",
                f"**[{song['title']}]({song['webpage_url']})**\n"
                f"Duration: `{_fmt_duration(song['duration'])}` • Position: **#{len(queue.songs)}**",
            )
            if song["thumbnail"]:
                embed.set_thumbnail(url=song["thumbnail"])
            await interaction.followup.send(embed=embed)
        else:
            queue.now_playing = song
            source = discord.FFmpegPCMAudio(song["url"], **FFMPEG_OPTS)
            source = discord.PCMVolumeTransformer(source, volume=queue.volume)
            vc.play(
                source,
                after=lambda e: asyncio.run_coroutine_threadsafe(
                    self._after_song(interaction.guild.id, e), self.bot.loop
                ),
            )
            embed = comprehensive_embed(
                title="🎵 Now Playing",
                description=f"**[{song['title']}]({song['webpage_url']})**",
                color=discord.Color.purple(),
            )
            embed.add_field(name="Duration", value=f"`{_fmt_duration(song['duration'])}`", inline=True)
            embed.add_field(name="Source", value=song["uploader"] or "Unknown", inline=True)
            embed.add_field(name="Volume", value=f"`{int(queue.volume * 100)}%`", inline=True)
            if song["thumbnail"]:
                embed.set_thumbnail(url=song["thumbnail"])
            await interaction.followup.send(embed=embed)

    # ── 2. Stop ───────────────────────────────────────────────────────────────

    @app_commands.command(name="stop", description="Stop playback and disconnect from voice.")
    async def stop(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if vc:
            self.queues.pop(interaction.guild.id, None)
            await vc.disconnect()
            await interaction.response.send_message(
                embed=success_embed("Stopped", "Disconnected from voice and cleared the queue.")
            )
        else:
            await interaction.response.send_message(
                embed=error_embed("Not Connected", "I'm not in a voice channel."), ephemeral=True
            )

    # ── 3. Skip ───────────────────────────────────────────────────────────────

    @app_commands.command(name="skip", description="Skip the current song.")
    async def skip(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if vc and (vc.is_playing() or vc.is_paused()):
            queue = self.get_queue(interaction.guild.id)
            title = queue.now_playing["title"] if queue.now_playing else "Unknown"
            vc.stop()
            await interaction.response.send_message(
                embed=success_embed("Skipped", f"Skipped **{title}**.")
            )
        else:
            await interaction.response.send_message(
                embed=error_embed("Nothing Playing", "There's nothing to skip."), ephemeral=True
            )

    # ── 4. Queue ──────────────────────────────────────────────────────────────

    @app_commands.command(name="queue", description="Show the current music queue.")
    async def queue_cmd(self, interaction: discord.Interaction):
        queue = self.get_queue(interaction.guild.id)
        embed = comprehensive_embed(title="🎶 Music Queue", color=discord.Color.purple())
        if queue.now_playing:
            embed.description = (
                f"**Now Playing:** [{queue.now_playing['title']}]({queue.now_playing['webpage_url']})"
                f" — `{_fmt_duration(queue.now_playing['duration'])}`\n\n"
            )
            flags = []
            if queue.loop:
                flags.append("🔁 Loop")
            if queue.shuffle:
                flags.append("🔀 Shuffle")
            if flags:
                embed.description += " • ".join(flags) + "\n\n"
            if queue.songs:
                lines = "\n".join(
                    f"`{i+1}.` [{s['title']}]({s['webpage_url']}) — `{_fmt_duration(s['duration'])}`"
                    for i, s in enumerate(queue.songs[:10])
                )
                embed.description += f"**Up Next:**\n{lines}"
                if len(queue.songs) > 10:
                    embed.description += f"\n*...and {len(queue.songs)-10} more*"
            else:
                embed.description += "*Queue is empty.*"
        else:
            embed.description = "Nothing is playing right now."
        embed.set_footer(text=f"Volume: {int(queue.volume*100)}%  •  XERO Music")
        await interaction.response.send_message(embed=embed)

    # ── 5. Pause ──────────────────────────────────────────────────────────────

    @app_commands.command(name="pause", description="Pause the current song.")
    async def pause(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if vc and vc.is_playing():
            vc.pause()
            await interaction.response.send_message(
                embed=success_embed("Paused", "Playback paused. Use `/music resume` to continue.")
            )
        elif vc and vc.is_paused():
            await interaction.response.send_message(
                embed=info_embed("Already Paused", "Use `/music resume` to continue."), ephemeral=True
            )
        else:
            await interaction.response.send_message(
                embed=error_embed("Nothing Playing", "There's nothing to pause."), ephemeral=True
            )

    # ── 6. Resume ─────────────────────────────────────────────────────────────

    @app_commands.command(name="resume", description="Resume a paused song.")
    async def resume(self, interaction: discord.Interaction):
        vc = interaction.guild.voice_client
        if vc and vc.is_paused():
            vc.resume()
            queue = self.get_queue(interaction.guild.id)
            title = queue.now_playing["title"] if queue.now_playing else "Unknown"
            await interaction.response.send_message(
                embed=success_embed("Resumed", f"Resumed **{title}**.")
            )
        elif vc and vc.is_playing():
            await interaction.response.send_message(
                embed=info_embed("Already Playing", "Music is already playing."), ephemeral=True
            )
        else:
            await interaction.response.send_message(
                embed=error_embed("Nothing Paused", "There's nothing to resume."), ephemeral=True
            )

    # ── 7. Volume ─────────────────────────────────────────────────────────────

    @app_commands.command(name="volume", description="Set the playback volume (1–100).")
    @app_commands.describe(level="Volume percentage (1–100)")
    async def volume(self, interaction: discord.Interaction, level: app_commands.Range[int, 1, 100]):
        queue = self.get_queue(interaction.guild.id)
        queue.volume = level / 100
        vc = interaction.guild.voice_client
        if vc and vc.source:
            try:
                vc.source.volume = queue.volume
            except Exception:
                pass
        await interaction.response.send_message(
            embed=success_embed("Volume Set", f"Volume set to **{level}%**.")
        )

    # ── 8. Now Playing ────────────────────────────────────────────────────────

    @app_commands.command(name="nowplaying", description="Show details about the current song.")
    async def nowplaying(self, interaction: discord.Interaction):
        queue = self.get_queue(interaction.guild.id)
        if not queue.now_playing:
            return await interaction.response.send_message(
                embed=error_embed("Nothing Playing", "No song is currently playing."), ephemeral=True
            )
        song = queue.now_playing
        embed = comprehensive_embed(
            title="🎵 Now Playing",
            description=f"**[{song['title']}]({song['webpage_url']})**",
            color=discord.Color.purple(),
        )
        embed.add_field(name="Duration", value=f"`{_fmt_duration(song['duration'])}`", inline=True)
        embed.add_field(name="Uploader", value=song.get("uploader", "Unknown"), inline=True)
        embed.add_field(name="Volume", value=f"`{int(queue.volume * 100)}%`", inline=True)
        embed.add_field(name="Queue", value=f"`{len(queue.songs)}` song(s) up next", inline=True)
        flags = []
        if queue.loop:
            flags.append("🔁 Loop On")
        if queue.shuffle:
            flags.append("🔀 Shuffle On")
        if flags:
            embed.add_field(name="Modes", value=" • ".join(flags), inline=True)
        if song.get("thumbnail"):
            embed.set_thumbnail(url=song["thumbnail"])
        await interaction.response.send_message(embed=embed)

    # ── 9. Loop ───────────────────────────────────────────────────────────────

    @app_commands.command(name="loop", description="Toggle loop mode for the current song.")
    async def loop(self, interaction: discord.Interaction):
        queue = self.get_queue(interaction.guild.id)
        queue.loop = not queue.loop
        state = "enabled" if queue.loop else "disabled"
        emoji = "🔁" if queue.loop else "➡️"
        await interaction.response.send_message(
            embed=success_embed(f"{emoji} Loop {state.capitalize()}", f"Loop mode is now **{state}**.")
        )

    # ── 10. Shuffle ───────────────────────────────────────────────────────────

    @app_commands.command(name="shuffle", description="Toggle shuffle mode for the queue.")
    async def shuffle(self, interaction: discord.Interaction):
        queue = self.get_queue(interaction.guild.id)
        queue.shuffle = not queue.shuffle
        state = "enabled" if queue.shuffle else "disabled"
        emoji = "🔀" if queue.shuffle else "➡️"
        await interaction.response.send_message(
            embed=success_embed(f"{emoji} Shuffle {state.capitalize()}", f"Shuffle mode is now **{state}**.")
        )

    # ── 11. Remove ────────────────────────────────────────────────────────────

    @app_commands.command(name="remove", description="Remove a song from the queue by position.")
    @app_commands.describe(position="Position in the queue to remove (1 = next song)")
    async def remove(self, interaction: discord.Interaction, position: app_commands.Range[int, 1, 100]):
        queue = self.get_queue(interaction.guild.id)
        if not queue.songs:
            return await interaction.response.send_message(
                embed=error_embed("Empty Queue", "The queue is already empty."), ephemeral=True
            )
        if position > len(queue.songs):
            return await interaction.response.send_message(
                embed=error_embed(
                    "Invalid Position",
                    f"Queue only has **{len(queue.songs)}** song(s).",
                ),
                ephemeral=True,
            )
        removed = queue.songs.pop(position - 1)
        await interaction.response.send_message(
            embed=success_embed("Removed", f"Removed **{removed['title']}** from position #{position}.")
        )

    # ── 12. Clear ─────────────────────────────────────────────────────────────

    @app_commands.command(name="clear", description="Clear all songs from the queue (keeps current song).")
    async def clear(self, interaction: discord.Interaction):
        queue = self.get_queue(interaction.guild.id)
        count = len(queue.songs)
        queue.songs.clear()
        if count == 0:
            await interaction.response.send_message(
                embed=info_embed("Queue Empty", "The queue was already empty.")
            )
        else:
            await interaction.response.send_message(
                embed=success_embed("Queue Cleared", f"Removed **{count}** song(s) from the queue.")
            )

    # ── 13. Lyrics ────────────────────────────────────────────────────────

    @app_commands.command(name="lyrics", description="Fetch lyrics for the current song or any song you name.")
    @app_commands.describe(query="Song to look up (leave empty to use the currently playing song)")
    async def lyrics(self, interaction: discord.Interaction, query: str = None):
        await interaction.response.defer()
        search = query
        if not search:
            queue = self.get_queue(interaction.guild.id)
            if queue.now_playing:
                search = queue.now_playing["title"]
            else:
                return await interaction.followup.send(
                    embed=error_embed("Nothing Playing", "Provide a song name or play something first."),
                )
        raw = search
        for trash in ["(official video)", "(official audio)", "(lyrics)", "(hd)", "(4k)", "(mv)",
                      "[official video]", "[official audio]", "[lyrics]", "official video",
                      "official audio", "official", "audio", "video", "lyrics", "hd", "4k"]:
            raw = raw.lower().replace(trash, "").strip()
        if " - " in raw:
            artist, title = raw.split(" - ", 1)
        elif " by " in raw:
            title, artist = raw.split(" by ", 1)
        else:
            artist = "unknown"
            title = raw.strip()
        artist = artist.strip()
        title = title.strip()
        lyrics_text = None
        tried = [(artist, title)]
        if artist == "unknown":
            tried = [(title, "")]
        for art, tit in tried:
            try:
                encoded_art = urllib.parse.quote(art)
                encoded_tit = urllib.parse.quote(tit or title)
                url = f"https://api.lyrics.ovh/v1/{encoded_art}/{encoded_tit}"
                async with aiohttp.ClientSession() as s:
                    async with s.get(url, timeout=aiohttp.ClientTimeout(total=8)) as r:
                        if r.status == 200:
                            data = await r.json()
                            lyrics_text = data.get("lyrics", "").strip()
                            if lyrics_text:
                                break
            except Exception:
                pass
        if not lyrics_text:
            return await interaction.followup.send(
                embed=error_embed(
                    "Lyrics Not Found",
                    f"Couldn't find lyrics for **{search}**.\nTry `/music lyrics query:Artist - Song Title`."
                )
            )
        chunks = [lyrics_text[i:i+3900] for i in range(0, min(len(lyrics_text), 11700), 3900)]
        embed = discord.Embed(
            title=f"🎵 {title.title()}",
            description=chunks[0],
            color=discord.Color.purple()
        )
        if artist and artist != "unknown":
            embed.set_author(name=artist.title())
        if len(chunks) > 1:
            embed.set_footer(text=f"Showing section 1/{len(chunks)}  •  XERO Music Lyrics")
        else:
            embed.set_footer(text="XERO Music Lyrics  •  via lyrics.ovh")
        await interaction.followup.send(embed=embed)


async def setup(bot: commands.Bot):
    await bot.add_cog(Music(bot))
