"""
XERO Bot — Voice AI
The most advanced feature XERO has. Bot joins your voice channel, listens,
understands what you say, thinks with Nemotron-3-Super, and talks back.

Full pipeline:
  1. User speaks → discord-ext-voice-recv captures Opus audio
  2. PCM audio buffered per user (3 seconds of silence = end of utterance)
  3. WAV sent to NVIDIA Parakeet-CTC-1.1B (STT) → transcript text
  4. Text + conversation history sent to Nemotron-3-Super → AI response
  5. Response text sent to NVIDIA FastPitch-HiFiGAN (TTS) → WAV audio
  6. WAV played back in voice channel via FFmpeg

NVIDIA APIs used:
  STT: nvidia/parakeet-ctc-1.1b
       https://ai.api.nvidia.com/v1/audio/nvidia/parakeet-ctc-1.1b
  TTS: nvidia/fastpitch-hifigan-tts
       https://ai.api.nvidia.com/v1/audio/nvidia/fastpitch-hifigan-tts
  LLM: nvidia/nemotron-3-super-120b-a12b (already in nvidia_api.py)

.env: NVIDIA_AUDIO_KEY (can reuse NVIDIA_MAIN_KEY if same NVIDIA account)

From the user's perspective:
  - Run /ai voice-join
  - Bot appears in your voice channel
  - Just talk naturally. "Hey XERO, what's the weather like?" or "Tell me a joke"
  - Bot processes what you said (~1-2 second latency) and talks back
  - Full conversation context maintained — it remembers what was said
  - /ai voice-leave to disconnect
"""
import discord, asyncio, io, os, wave, struct, logging, aiohttp, tempfile, base64
import numpy as np
from discord.ext import commands
from discord import app_commands
from utils.embeds import success_embed, error_embed, info_embed, XERO, comprehensive_embed

try:
    import discord.ext.voice_recv as vr
    VOICE_RECV_AVAILABLE = True
except ImportError:
    VOICE_RECV_AVAILABLE = False

logger = logging.getLogger("XERO.VoiceAI")

# ── Audio constants ────────────────────────────────────────────────────────────
SAMPLE_RATE    = 48000   # Discord sends 48kHz
CHANNELS       = 2       # Discord sends stereo
BYTES_PER_SAMPLE = 2     # 16-bit
# 3 seconds silence threshold to detect end of speech
SILENCE_THRESHOLD    = 500    # RMS amplitude below this = silence
SILENCE_DURATION_S   = 1.2    # seconds of silence before processing
BUFFER_MAX_S         = 8.0    # max buffer before forcing process (cuts off at 8s)
MIN_SPEECH_S         = 0.3    # ignore utterances shorter than this

# Active sessions: guild_id -> VoiceAISession
SESSIONS: dict = {}


class VoiceAISession:
    """Manages a voice AI session for one guild."""

    def __init__(self, bot, guild_id: int, text_channel: discord.TextChannel):
        self.bot          = bot
        self.guild_id     = guild_id
        self.text_channel = text_channel
        self.audio_buffer: dict = {}   # user_id -> list of PCM byte chunks
        self.silence_counter: dict = {}  # user_id -> frames of silence
        self.is_speaking: dict = {}    # user_id -> bool
        self.processing: dict = {}     # user_id -> bool (prevent double-process)
        self.conversation: list = []   # conversation history for context
        self.voice_client = None
        self._lock = asyncio.Lock()

    def add_audio(self, user_id: int, pcm_data: bytes):
        """Called for every 20ms audio packet from a user."""
        if user_id not in self.audio_buffer:
            self.audio_buffer[user_id]    = []
            self.silence_counter[user_id] = 0
            self.is_speaking[user_id]     = False
            self.processing[user_id]      = False

        # Calculate RMS amplitude to detect speech vs silence
        if len(pcm_data) >= 2:
            samples = np.frombuffer(pcm_data, dtype=np.int16)
            rms = np.sqrt(np.mean(samples.astype(np.float32) ** 2))
        else:
            rms = 0

        frames_per_packet  = len(pcm_data) / (BYTES_PER_SAMPLE * CHANNELS)
        packet_duration_s  = frames_per_packet / SAMPLE_RATE

        if rms > SILENCE_THRESHOLD:
            # Speech detected
            self.audio_buffer[user_id].append(pcm_data)
            self.silence_counter[user_id] = 0
            self.is_speaking[user_id]     = True
        elif self.is_speaking[user_id]:
            # Was speaking, now silent — accumulate silence buffer
            self.audio_buffer[user_id].append(pcm_data)
            self.silence_counter[user_id] += packet_duration_s

            # End of utterance detected
            if self.silence_counter[user_id] >= SILENCE_DURATION_S:
                if not self.processing.get(user_id, False):
                    audio_data = b"".join(self.audio_buffer[user_id])
                    self.audio_buffer[user_id]    = []
                    self.silence_counter[user_id] = 0
                    self.is_speaking[user_id]     = False
                    self.processing[user_id]      = True
                    asyncio.create_task(self._process_utterance(user_id, audio_data))

            # Force-process if buffer too long
            total_s = len(b"".join(self.audio_buffer[user_id])) / (SAMPLE_RATE * CHANNELS * BYTES_PER_SAMPLE)
            if total_s >= BUFFER_MAX_S and not self.processing.get(user_id, False):
                audio_data = b"".join(self.audio_buffer[user_id])
                self.audio_buffer[user_id]    = []
                self.silence_counter[user_id] = 0
                self.is_speaking[user_id]     = False
                self.processing[user_id]      = True
                asyncio.create_task(self._process_utterance(user_id, audio_data))

    async def _process_utterance(self, user_id: int, pcm_data: bytes):
        """Full pipeline: audio → STT → LLM → TTS → play."""
        try:
            guild  = self.bot.get_guild(self.guild_id)
            member = guild.get_member(user_id) if guild else None

            # Minimum speech check
            duration_s = len(pcm_data) / (SAMPLE_RATE * CHANNELS * BYTES_PER_SAMPLE)
            if duration_s < MIN_SPEECH_S:
                return

            # ── Step 1: PCM → WAV (16kHz mono for ASR) ────────────────────
            wav_bytes = self._pcm_to_wav_16k(pcm_data)

            # ── Step 2: STT — NVIDIA Parakeet ─────────────────────────────
            transcript = await self._stt(wav_bytes)
            if not transcript or len(transcript.strip()) < 2:
                return

            name = member.display_name if member else f"User {user_id}"
            logger.info(f"Voice STT [{name}]: {transcript}")

            # Show transcript in text channel
            try:
                await self.text_channel.send(
                    embed=discord.Embed(
                        description=f"🎙️ **{name}:** {transcript}",
                        color=XERO.SECONDARY
                    )
                )
            except Exception:
                pass

            # ── Step 3: LLM — Nemotron-3-Super ────────────────────────────
            self.conversation.append({"role": "user", "content": f"[{name}]: {transcript}"})
            if len(self.conversation) > 20:
                self.conversation = self.conversation[-20:]

            system = (
                "You are XERO, a helpful AI assistant speaking in a Discord voice channel. "
                "Keep responses SHORT and conversational — 1-3 sentences max. "
                "You are speaking out loud so do NOT use markdown, asterisks, or lists. "
                "Sound natural, like a real person talking."
            )
            response_text = await self.bot.nvidia.chat_with_context(
                self.conversation, transcript, "neutral",
                user_name   = name,
                server_name = guild.name if guild else ""
            )

            if not response_text:
                return

            self.conversation.append({"role": "assistant", "content": response_text})
            logger.info(f"Voice LLM response: {response_text[:80]}")

            # Show response in text channel
            try:
                await self.text_channel.send(
                    embed=discord.Embed(
                        description=f"🤖 **XERO:** {response_text}",
                        color=XERO.PRIMARY
                    )
                )
            except Exception:
                pass

            # ── Step 4: TTS — NVIDIA FastPitch ────────────────────────────
            audio_bytes = await self._tts(response_text)
            if not audio_bytes:
                logger.warning("TTS returned no audio")
                return

            # ── Step 5: Play audio in voice channel ────────────────────────
            await self._play_audio(audio_bytes)

        except Exception as e:
            logger.error(f"Voice AI pipeline error: {e}")
        finally:
            self.processing[user_id] = False

    def _pcm_to_wav_16k(self, pcm_data: bytes) -> bytes:
        """Convert Discord's 48kHz stereo PCM to 16kHz mono WAV."""
        # Stereo to mono
        arr = np.frombuffer(pcm_data, dtype=np.int16)
        if len(arr) % 2 == 0:
            arr = arr.reshape(-1, 2).mean(axis=1).astype(np.int16)
        # Downsample 48k → 16k
        arr_16k = arr[::3]
        buf = io.BytesIO()
        with wave.open(buf, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(16000)
            wf.writeframes(arr_16k.tobytes())
        return buf.getvalue()

    async def _stt(self, wav_bytes: bytes) -> str | None:
        """NVIDIA Parakeet-CTC-1.1B Speech-to-Text."""
        api_key = os.getenv("NVIDIA_AUDIO_KEY") or os.getenv("NVIDIA_MAIN_KEY", "")
        if not api_key:
            return None
        try:
            # Encode WAV as base64 for API
            wav_b64 = base64.b64encode(wav_bytes).decode("utf-8")
            payload = {
                "input": wav_b64,
                "model": "nvidia/parakeet-ctc-1.1b",
                "encoding": "LINEAR_PCM",
                "sample_rate_hertz": 16000,
                "language_code": "en-US"
            }
            headers = {
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
            }
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    "https://ai.api.nvidia.com/v1/audio/nvidia/parakeet-ctc-1.1b",
                    json=payload,
                    headers=headers,
                    timeout=aiohttp.ClientTimeout(total=15)
                ) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        # Response format: {"text": "transcribed text"} or {"results": [{"transcript": "..."}]}
                        text = (data.get("text") or
                                (data.get("results", [{}])[0].get("transcript", "")) or
                                data.get("transcript", ""))
                        return text.strip() if text else None
                    else:
                        err = await resp.text()
                        logger.error(f"STT API {resp.status}: {err[:200]}")
                        return None
        except Exception as e:
            logger.error(f"STT error: {e}")
            return None

    async def _tts(self, text: str) -> bytes | None:
        """NVIDIA FastPitch-HiFiGAN Text-to-Speech."""
        api_key = os.getenv("NVIDIA_AUDIO_KEY") or os.getenv("NVIDIA_MAIN_KEY", "")
        if not api_key:
            return None
        try:
            # Clean text for TTS (remove any markdown)
            import re
            clean = re.sub(r"[*_`#\[\]]", "", text).strip()
            clean = clean[:400]  # Cap length for voice

            payload = {
                "text": clean,
                "voice": "English-US.Female-1",  # or "English-US.Male-1"
                "quality": "22050",
                "encoding": "LINEAR_PCM",
                "sample_rate_hertz": 22050
            }
            headers = {
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
                "Accept": "audio/wav",
            }
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    "https://ai.api.nvidia.com/v1/audio/nvidia/fastpitch-hifigan-tts",
                    json=payload,
                    headers=headers,
                    timeout=aiohttp.ClientTimeout(total=20)
                ) as resp:
                    if resp.status == 200:
                        content_type = resp.content_type or ""
                        audio_bytes  = await resp.read()
                        if audio_bytes:
                            # If it's not a WAV, wrap it
                            if not audio_bytes.startswith(b"RIFF"):
                                audio_bytes = self._pcm_to_wav_direct(audio_bytes, 22050)
                            return audio_bytes
                    else:
                        err = await resp.text()
                        logger.error(f"TTS API {resp.status}: {err[:200]}")
                        return None
        except Exception as e:
            logger.error(f"TTS error: {e}")
            return None

    def _pcm_to_wav_direct(self, pcm: bytes, sample_rate: int = 22050) -> bytes:
        buf = io.BytesIO()
        with wave.open(buf, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(sample_rate)
            wf.writeframes(pcm)
        return buf.getvalue()

    async def _play_audio(self, wav_bytes: bytes):
        """Play WAV audio in the voice channel via FFmpeg."""
        if not self.voice_client or not self.voice_client.is_connected():
            return
        # Wait if already playing
        waited = 0
        while self.voice_client.is_playing() and waited < 10:
            await asyncio.sleep(0.5)
            waited += 0.5

        try:
            # Write to temp file for FFmpeg
            with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as f:
                f.write(wav_bytes)
                tmppath = f.name

            source = discord.FFmpegPCMAudio(
                tmppath,
                options="-vn",
                before_options="-loglevel quiet"
            )
            source = discord.PCMVolumeTransformer(source, volume=0.9)

            def after_play(error):
                try:
                    os.unlink(tmppath)
                except Exception:
                    pass
                if error:
                    logger.error(f"Voice playback: {error}")

            self.voice_client.play(source, after=after_play)
        except Exception as e:
            logger.error(f"Audio playback: {e}")


# ── XERO Voice AI sink (captures audio per user) ──────────────────────────────

if VOICE_RECV_AVAILABLE:
    class XEROVoiceSink(vr.AudioSink):
        """Receives raw audio from every user in the channel."""

        def __init__(self, session: VoiceAISession):
            super().__init__()
            self.session = session

        def wants_opus(self) -> bool:
            return False  # Give us decoded PCM

        def write(self, user: discord.User, data: vr.VoiceData):
            if user and not user.bot:
                self.session.add_audio(user.id, data.pcm)

        def cleanup(self):
            pass


# ── Voice AI Commands ─────────────────────────────────────────────────────────

class VoiceAI(commands.GroupCog, name="ai-voice"):
    def __init__(self, bot):
        self.bot = bot

    @app_commands.command(name="join", description="XERO joins your voice channel and listens. Talk naturally and it talks back.")
    @app_commands.describe(
        language="Language (default: English)",
        voice_style="XERO's voice character"
    )
    @app_commands.choices(voice_style=[
        app_commands.Choice(name="Natural Female",  value="English-US.Female-1"),
        app_commands.Choice(name="Natural Male",    value="English-US.Male-1"),
    ])
    async def voice_join(self, interaction: discord.Interaction,
                         language: str = "English",
                         voice_style: str = "English-US.Female-1"):

        if not VOICE_RECV_AVAILABLE:
            return await interaction.response.send_message(embed=error_embed(
                "Voice Receive Unavailable",
                "Install `discord-ext-voice-recv` to enable voice AI.\n"
                "`pip install discord-ext-voice-recv`"
            ))

        api_key = os.getenv("NVIDIA_AUDIO_KEY") or os.getenv("NVIDIA_MAIN_KEY", "")
        if not api_key:
            return await interaction.response.send_message(embed=error_embed(
                "NVIDIA Audio Key Missing",
                "Add `NVIDIA_AUDIO_KEY` to your `.env` file.\n"
                "Get it from: https://build.nvidia.com\n"
                "*(You can reuse `NVIDIA_MAIN_KEY` if it's the same account)*"
            ))

        if not interaction.user.voice or not interaction.user.voice.channel:
            return await interaction.response.send_message(embed=error_embed(
                "Join a Voice Channel",
                "You need to be in a voice channel first."
            ))

        if interaction.guild.id in SESSIONS:
            return await interaction.response.send_message(embed=error_embed(
                "Already Active",
                f"Voice AI is already running. Use `/ai-voice leave` to stop it."
            ))

        await interaction.response.defer()
        vc_channel = interaction.user.voice.channel

        try:
            # Connect using voice-recv VoiceClient
            vc = await vc_channel.connect(cls=vr.VoiceRecvClient)

            session = VoiceAISession(self.bot, interaction.guild.id, interaction.channel)
            session.voice_client = vc
            SESSIONS[interaction.guild.id] = session

            # Start listening
            sink = XEROVoiceSink(session)
            vc.listen(sink)

            embed = discord.Embed(
                title="🎙️  XERO Voice AI — Active",
                description=(
                    f"Listening in **{vc_channel.name}**\n\n"
                    f"Just talk naturally. I'll hear you, think, and talk back.\n\n"
                    f"**Tips:**\n"
                    f"• Speak clearly, wait ~1 second after finishing\n"
                    f"• Keep questions under 15 seconds\n"
                    f"• I remember our full conversation\n"
                    f"• Transcripts + responses appear here in text\n\n"
                    f"*Powered by NVIDIA Parakeet STT + Nemotron-3-Super + FastPitch TTS*"
                ),
                color=XERO.PRIMARY
            )
            embed.add_field(name="🔊 Voice",    value=vc_channel.mention,  inline=True)
            embed.add_field(name="🗣️ Style",   value=voice_style,          inline=True)
            embed.add_field(name="🌐 Language",value=language,              inline=True)
            embed.set_footer(text="Say anything • /ai-voice leave to stop")
            await interaction.followup.send(embed=embed)

        except Exception as e:
            await interaction.followup.send(embed=error_embed(
                "Connection Failed", f"Couldn't connect: {str(e)}"
            ))

    @app_commands.command(name="leave", description="XERO leaves the voice channel and ends the session.")
    async def voice_leave(self, interaction: discord.Interaction):
        session = SESSIONS.get(interaction.guild.id)
        if not session:
            return await interaction.response.send_message(embed=error_embed(
                "Not Active", "No voice AI session is running in this server."
            ))

        try:
            if session.voice_client and session.voice_client.is_connected():
                await session.voice_client.disconnect()
        except Exception:
            pass

        SESSIONS.pop(interaction.guild.id, None)

        lines = len(session.conversation) // 2
        await interaction.response.send_message(embed=success_embed(
            "🎙️  Voice AI — Ended",
            f"Session complete.\n"
            f"**Exchanges:** {lines}\n"
            f"*Conversation context cleared.*"
        ))

    @app_commands.command(name="status", description="Check the current voice AI session status.")
    async def voice_status(self, interaction: discord.Interaction):
        session = SESSIONS.get(interaction.guild.id)
        if not session:
            return await interaction.response.send_message(embed=info_embed(
                "No Active Session",
                "Use `/ai-voice join` to start a voice AI session."
            ))

        vc = session.voice_client
        ch_name = vc.channel.name if vc and vc.channel else "?"
        lines   = len(session.conversation) // 2
        listeners = [m for m in (vc.channel.members if vc and vc.channel else []) if not m.bot]

        embed = comprehensive_embed(title="🎙️  Voice AI — Active", color=XERO.SUCCESS)
        embed.add_field(name="📢 Channel",    value=f"**{ch_name}**",      inline=True)
        embed.add_field(name="💬 Exchanges",  value=str(lines),             inline=True)
        embed.add_field(name="👥 Listeners",  value=str(len(listeners)),    inline=True)
        embed.set_footer(text="XERO Voice AI  •  /ai-voice leave to stop")
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="clear", description="Clear the voice AI conversation memory without leaving.")
    async def voice_clear(self, interaction: discord.Interaction):
        session = SESSIONS.get(interaction.guild.id)
        if not session:
            return await interaction.response.send_message(embed=error_embed(
                "No Session", "No active voice session."
            ))
        session.conversation.clear()
        await interaction.response.send_message(embed=success_embed(
            "Memory Cleared", "Conversation history reset. XERO starts fresh."
        ))


async def setup(bot):
    if not VOICE_RECV_AVAILABLE:
        logger.warning("discord-ext-voice-recv not installed. Voice AI disabled. pip install discord-ext-voice-recv")
    await bot.add_cog(VoiceAI(bot))
