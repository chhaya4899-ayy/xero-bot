"""
XERO Bot — AI Engine
──────────────────────────────────────────────────────────────
Model routing:
  Primary  → nvidia/nemotron-3-super-120b-a12b  (NVIDIA_MAIN_KEY)
             All text: chat, reason, code, translate, brainstorm, etc.
             1M token context window.

  Vision   → nvidia/llama-3.1-nemotron-nano-vl-8b-v1  (NVIDIA_VISION_KEY)
             Reads images only. Describes them, passes to Primary to respond.

  Images   → Pollinations.ai  (no key needed)
             Free FLUX-based image generation via URL.
──────────────────────────────────────────────────────────────
"""
import aiohttp
import asyncio
import logging
import urllib.parse
from typing import Optional, List, Dict

logger = logging.getLogger("XERO.AI")

BASE_URL       = "https://integrate.api.nvidia.com/v1/chat/completions"
MODEL_PRIMARY  = "nvidia/nemotron-3-super-120b-a12b"
MODEL_VISION   = "nvidia/llama-3.1-nemotron-nano-vl-8b-v1"

SYSTEM_BASE = (
    "You are XERO, an advanced AI-powered Discord bot created by Team Flame. "
    "You're sharp, direct, and genuinely helpful with a confident personality. "
    "Use Discord markdown formatting. Keep chat responses concise — under 400 words "
    "unless the user explicitly needs something longer like code or analysis."
)

PERSONA_EXTRAS = {
    "neutral":    "",
    "friendly":   "Be warm, casual, enthusiastic. Use emojis occasionally.",
    "analytical": "Be highly detailed, data-driven, and methodical. Show your reasoning.",
    "sarcastic":  "Be clever and witty. Light sarcasm is fine — never mean.",
    "mentor":     "Be wise and encouraging. Help people grow.",
}


class NvidiaAPI:
    def __init__(self, primary_key: str, vision_key: str = None):
        self.primary_key = primary_key
        self.vision_key  = vision_key or primary_key

    # ── Core caller ───────────────────────────────────────────────────────

    async def _call(
        self,
        messages:    List[Dict],
        max_tokens:  int   = 1024,
        temperature: float = 0.7,
        use_vision:  bool  = False,
    ) -> Optional[str]:
        """Routes to the right model + key. Returns response text or an error string."""
        api_key = self.vision_key if use_vision else self.primary_key
        model   = MODEL_VISION    if use_vision else MODEL_PRIMARY

        if not api_key:
            return "⚠️ NVIDIA API key not set. Add `NVIDIA_MAIN_KEY` to your `.env` file."

        headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type":  "application/json",
        }
        payload = {
            "model":       model,
            "messages":    messages,
            "max_tokens":  max_tokens,
            "temperature": temperature,
            "stream":      False,
        }

        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    BASE_URL, headers=headers, json=payload,
                    timeout=aiohttp.ClientTimeout(total=45)
                ) as resp:
                    if resp.status == 200:
                        data = await resp.json()
                        content = data["choices"][0]["message"]["content"]
                        if not content:
                            return "⚠️ AI returned an empty response. Try rephrasing."
                        return content
                    elif resp.status == 401:
                        logger.error("NVIDIA API: 401 Unauthorized — check your API key")
                        return "❌ Invalid API key. Check your `NVIDIA_MAIN_KEY` in `.env`."
                    elif resp.status == 402:
                        return "⚠️ NVIDIA API Credits exhausted. Please check your account."
                    elif resp.status == 429:
                        logger.warning("NVIDIA API: 429 Rate limited")
                        return "⏳ Rate limited. Try again in a few seconds."
                    else:
                        err = await resp.text()
                        logger.error(f"NVIDIA API {resp.status}: {err[:300]}")
                        return f"API error ({resp.status}). Try again."
        except asyncio.TimeoutError:
            logger.warning("NVIDIA API: timeout")
            return "⌛ AI is taking too long (45s+). Try again in a moment."
        except Exception as e:
            logger.error(f"NVIDIA API exception: {e}")
            return f"❌ Connection error: {str(e)[:100]}"

    # ── Vision pipeline ───────────────────────────────────────────────────

    async def analyze_image_url(self, image_url: str, question: str = "Describe this image in detail.") -> str:
        """
        Two-step pipeline:
          1. Nano VL (vision key) reads the image → detailed description
          2. Nemotron Super (primary key) uses that description to answer the question
        """
        # Step 1 — Vision model reads the image
        vision_msgs = [{
            "role": "user",
            "content": [
                {
                    "type": "text",
                    "text": (
                        "You are an image analysis assistant. "
                        "Describe this image comprehensively: every visible object, "
                        "text, person, color, layout, and context. Be factual and thorough."
                    )
                },
                {
                    "type":      "image_url",
                    "image_url": {"url": image_url}
                },
            ]
        }]

        vision_desc = await self._call(
            vision_msgs, max_tokens=700, temperature=0.2, use_vision=True
        )

        if not vision_desc or vision_desc.startswith(("❌", "⚠️", "⌛", "API error")):
            return f"Could not read the image. Vision model error: {vision_desc}"

        # Step 2 — Primary model answers using the visual description
        final_msgs = [
            {"role": "system", "content": SYSTEM_BASE},
            {
                "role": "user",
                "content": (
                    f"[Image content from visual analysis]:\n{vision_desc}\n\n"
                    f"[User's question about the image]:\n{question}"
                )
            },
        ]
        return await self._call(final_msgs, max_tokens=900, temperature=0.7) or None

    # ── Image generation (Pollinations.ai — no key) ───────────────────────

    @staticmethod
    def image_url(prompt: str, model: str = "flux", width: int = 1024, height: int = 1024, seed: int = None) -> str:
        """
        Returns a Pollinations.ai image URL. No API key needed.
        Supports: flux, flux-realism, flux-anime, flux-3d, turbo
        Just embed this URL in a Discord embed.set_image().
        """
        import random
        encoded = urllib.parse.quote(prompt)
        s       = seed or random.randint(1, 999999)
        return (
            f"https://image.pollinations.ai/prompt/{encoded}"
            f"?width={width}&height={height}&seed={s}&model={model}&nologo=true"
        )

    # ── @mention chat (real channel context) ─────────────────────────────

    async def chat_with_context(
        self,
        history: List[Dict],
        message: str,
        persona: str = "neutral",
        user_name: str = "",
        channel_name: str = "",
        server_name: str = "",
    ) -> str:
        """
        Used for @XERO mentions. Builds a rich system prompt with:
        - Full channel history (last 15 real messages)
        - Server / channel / user context
        - Persona-based personality
        """
        extra   = PERSONA_EXTRAS.get(persona, "")
        context = ""
        if server_name:  context += f"Server: {server_name}. "
        if channel_name: context += f"Channel: #{channel_name}. "
        if user_name:    context += f"Talking to: {user_name}. "

        system = (
            f"{SYSTEM_BASE} {extra} "
            f"{context}"
            "You can see recent chat history above for context — use it to give relevant, "
            "grounded answers. If someone asks 'what did X say' or 'what was that link', "
            "look in the history above."
        )

        msgs = [{"role": "system", "content": system}]
        # Include full history (already reversed to oldest-first in events.py)
        msgs.extend(history)
        msgs.append({"role": "user", "content": message})

        return await self._call(msgs, max_tokens=800, temperature=0.75) or None

    # ── All text methods (primary model) ─────────────────────────────────

    async def ask(self, question: str, system: str = None) -> str:
        msgs = [
            {"role": "system", "content": system or SYSTEM_BASE},
            {"role": "user",   "content": question},
        ]
        return await self._call(msgs, max_tokens=1500) or None

    async def summarize(self, text: str) -> str:
        msgs = [
            {"role": "system", "content": f"{SYSTEM_BASE} Summarize clearly and concisely, covering all key points. Use bullet points for clarity."},
            {"role": "user",   "content": text},
        ]
        return await self._call(msgs, max_tokens=700, temperature=0.4) or None

    async def translate(self, text: str, language: str) -> str:
        msgs = [
            {"role": "system", "content": f"{SYSTEM_BASE} Translate the following text to {language}. Return ONLY the translation, nothing else."},
            {"role": "user",   "content": text},
        ]
        return await self._call(msgs, max_tokens=900, temperature=0.2) or None

    async def brainstorm(self, topic: str, count: int = 10) -> str:
        msgs = [
            {"role": "system", "content": f"{SYSTEM_BASE} Generate exactly {count} creative, unique, detailed ideas as a numbered list. For each idea include a 1-2 sentence explanation."},
            {"role": "user",   "content": f"Topic: {topic}"},
        ]
        return await self._call(msgs, max_tokens=1400, temperature=0.9) or None

    async def explain_code(self, code: str) -> str:
        msgs = [
            {
                "role": "system",
                "content": (
                    f"{SYSTEM_BASE} You are an expert programmer. Explain this code: "
                    "what it does, how it works line by line, time/space complexity, "
                    "potential bugs, and improvement suggestions."
                )
            },
            {"role": "user", "content": f"```\n{code}\n```"},
        ]
        return await self._call(msgs, max_tokens=1400, temperature=0.3) or "Failed."

    async def debug_code(self, code: str, error: str = "") -> str:
        prompt = f"Code:\n```\n{code}\n```"
        if error:
            prompt += f"\n\nError message:\n{error}"
        msgs = [
            {
                "role": "system",
                "content": (
                    f"{SYSTEM_BASE} You are an expert debugger. "
                    "Find every bug, explain the root cause of each, "
                    "and provide the fully corrected code with comments."
                )
            },
            {"role": "user", "content": prompt},
        ]
        return await self._call(msgs, max_tokens=1600, temperature=0.3) or "Failed."

    async def analyze_sentiment(self, text: str) -> str:
        msgs = [
            {
                "role": "system",
                "content": (
                    f"{SYSTEM_BASE} Perform deep sentiment analysis. Cover: "
                    "overall sentiment (positive/negative/neutral), confidence %, "
                    "emotional breakdown, tone, key phrases that drove the analysis, "
                    "and how a reader would likely feel after reading it."
                )
            },
            {"role": "user", "content": text},
        ]
        return await self._call(msgs, max_tokens=700, temperature=0.3) or "Failed."

    async def rewrite(self, text: str, style: str) -> str:
        msgs = [
            {"role": "system", "content": f"{SYSTEM_BASE} Rewrite the following text in a {style} style. Keep the original meaning exactly — only change the tone, vocabulary, and structure."},
            {"role": "user",   "content": text},
        ]
        return await self._call(msgs, max_tokens=900, temperature=0.7) or "Failed."

    async def check_grammar(self, text: str) -> str:
        msgs = [
            {
                "role": "system",
                "content": (
                    f"{SYSTEM_BASE} Check this text for grammar, spelling, punctuation, and style. "
                    "List every issue found with the rule being violated, "
                    "then provide the fully corrected version at the end."
                )
            },
            {"role": "user", "content": text},
        ]
        return await self._call(msgs, max_tokens=900, temperature=0.2) or "Failed."

    async def generate(self, prompt: str, max_tokens: int = 1400) -> str:
        msgs = [
            {"role": "system", "content": f"{SYSTEM_BASE} Generate creative, engaging, high-quality content based on the prompt. Be thorough and detailed."},
            {"role": "user",   "content": prompt},
        ]
        return await self._call(msgs, max_tokens=max_tokens, temperature=0.85) or "Failed."

    async def fact_check(self, claim: str) -> str:
        msgs = [
            {
                "role": "system",
                "content": (
                    f"{SYSTEM_BASE} Fact-check this claim thoroughly. "
                    "Provide: 1) Verdict (True/False/Partially True/Unverifiable), "
                    "2) Detailed explanation with reasoning, "
                    "3) Key evidence or counterevidence, "
                    "4) Important context a reader should know."
                )
            },
            {"role": "user", "content": f"Claim to fact-check: {claim}"},
        ]
        return await self._call(msgs, max_tokens=900, temperature=0.2) or "Failed."

    async def roast(self, target: str) -> str:
        msgs = [
            {
                "role": "system",
                "content": (
                    f"{SYSTEM_BASE} Write a funny, clever, playful roast. "
                    "Keep it lighthearted and entertaining — sharp wit, not genuine meanness. "
                    "2-3 sentences max."
                )
            },
            {"role": "user", "content": f"Roast subject: {target}"},
        ]
        return await self._call(msgs, max_tokens=300, temperature=0.95) or "Failed."
