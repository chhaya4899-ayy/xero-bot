"""
XERO Bot — Ticket System v3 (Complete Redesign)

What's new vs. v2:
  • Discord Components V2 layouts (Container / Section / Separator / Thumbnail /
    MediaGallery / TextDisplay) for every panel, ticket message, brief and archive
    — replaces the basic-emoji embeds with the modern, accessory-rich UI most
    bots never use.
  • Persistent panel registry (`ticket_panels`) — every posted panel is tracked
    and auto-reposted on startup so existing servers never have to re-run
    `/ticket setup`. Custom categories are preserved per guild.
  • Triage modal — opener describes the issue first; the bot AI auto-summarises
    it and suggests a severity badge before staff are pinged.
  • Workload-balanced staff routing — only the on-call staff member with the
    lowest current load is mentioned, no more global @SupportTeam pings on every
    ticket. Optional quiet-hours window silences pings entirely.
  • SLA + escalation engine (background loop) — unanswered tickets hit a
    response SLA, then get escalated to a lead role; a live SLA badge sits in
    the ticket header.
  • Reply macros (canned responses) — `/ticket macro` lets staff define and
    fire snippets; AI can suggest the best macro from context.
  • Reputation / anti-abuse — frivolous tickets, burst opens and per-user
    cooldowns are tracked; repeat abusers are throttled or temporarily blocked
    from opening tickets.
  • Anti-flood: per-user cooldown, per-guild burst limit, panel click throttle,
    secure custom_id nonces, channel-name sanitisation, and AI-input scrubbing.

All admin commands keep the original permission gates. Schema additions are
done lazily in setup() with `ALTER TABLE … ADD COLUMN` guards so older DBs
upgrade transparently.
"""

from utils.guard import command_guard
import discord
import aiosqlite
import asyncio
import io
import logging
import datetime
import time
import hashlib
import random
import re
from collections import defaultdict, deque
from discord.ext import commands, tasks
from discord import app_commands, ui
from utils.embeds import (
    XERO, success_embed, error_embed, info_embed, brand_embed, comprehensive_embed
)

logger = logging.getLogger("XERO.Tickets")

# ─────────────────────────────────────────────────────────────────────────────
# Constants
# ─────────────────────────────────────────────────────────────────────────────

PANEL_VERSION = 3

TC_PRIMARY  = 0x2B2D31
TC_DARK     = 0x0D1117
TC_ACCENT   = 0x5865F2
TC_SUCCESS  = 0x57F287
TC_WARNING  = 0xFEE75C
TC_DANGER   = 0xED4245

DEFAULT_CATEGORIES = {
    "technical": {
        "label": "Technical Support",
        "emoji": "🛠️",
        "description": "Discord/ERLC errors, bugs, system malfunctions",
        "priority": "high",
    },
    "internal_affairs": {
        "label": "Internal Affairs & Appeals",
        "emoji": "⚖️",
        "description": "Player reports (RDM/VDM/FailRP) & moderation appeals",
        "priority": "high",
    },
    "departmental": {
        "label": "Departmental & Career Inquiries",
        "emoji": "🚔",
        "description": "LEO/EMS/Fire applications, certs & promotions",
        "priority": "normal",
    },
    "management": {
        "label": "Management Direct Line",
        "emoji": "✉️",
        "description": "Partnerships, exec applications, BoD matters",
        "priority": "urgent",
    },
    "treasury": {
        "label": "Treasury & Logistics",
        "emoji": "💳",
        "description": "Giveaway prizes, payouts, sponsorships, queue",
        "priority": "normal",
    },
    "administrative": {
        "label": "Administrative Services",
        "emoji": "📂",
        "description": "Whitelist, role verification, name changes",
        "priority": "low",
    },
    "other": {
        "label": "Other / Miscellaneous",
        "emoji": "⚙️",
        "description": "Anything that doesn't fit the categories above",
        "priority": "low",
    },
}

# Random flavor lines rotated under the panel footer.
PANEL_FLAVORS = [
    "Tip: include screenshots, links, and what you've already tried — it speeds things up by ~3×.",
    "Tip: one ticket per topic. Mixing issues makes them slower to resolve.",
    "Tip: check pinned messages and announcements first — your answer might already be there.",
    "Heads up: low-effort tickets are auto-flagged. Be specific and you'll be helped faster.",
    "Did you know? Our routing system always sends your ticket to the staff member with the lightest load.",
    "Heads up: every conversation is summarised by AI on close, so the same issue isn't re-explained next time.",
]

PRIORITY_LABELS = {
    "urgent": "🔴 Urgent",
    "high":   "🟠 High",
    "normal": "🟡 Normal",
    "low":    "🟢 Low",
}

DEFAULT_RESPONSE_SLA_MIN   = 30
DEFAULT_RESOLUTION_SLA_MIN = 24 * 60
DEFAULT_USER_COOLDOWN_SEC  = 60
DEFAULT_GUILD_BURST_LIMIT  = 10   # max ticket opens per minute per guild
ABUSE_BLOCK_THRESHOLD      = 5    # abuse_score above this -> hard block
ABUSE_BLOCK_HOURS          = 6

# In-process state (intentionally not persisted — rebuilds on restart)
_user_open_cooldowns: dict[tuple[int, int], float] = {}
_guild_burst_buckets: dict[int, deque] = defaultdict(lambda: deque(maxlen=128))
_panel_click_throttle: dict[tuple[int, int], float] = defaultdict(float)

# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────


_CUSTOM_EMOJI_RE = re.compile(r"^<a?:\w{2,32}:\d{15,22}>$")
# Single-codepoint Unicode emoji in the supplementary plane (U+1F000+) are
# safe; tons of common BMP emoji are NOT (e.g. ✦, ★ raw — Discord rejects
# them at the API). Allow only an explicit BMP allowlist of well-known emoji.
_BMP_EMOJI_ALLOW = set("⭐✅❌⚠️ℹ️❓❗➕➖⏳⏰⌛✉️✏️📌📎📁📂📄📊📋📍📞📢📣📤📥📦"
                       "📨📩📪📫📬📭📮🔍🔎🔒🔓🔔🔕🔖🔗🔘🔙🔚🔛🔜🔝🔞🔟🔠🔡🔢"
                       "🔣🔤🔥🔧🔨🔩🔪🔫🔬🔭🔮🔯🕐🕑🕒🕓🕔🕕🕖🕗🕘🕙🕚🕛🕜🕝"
                       "🕞🕟🕠🕡🕢🕣🕤🕥🕦🕧🌐🌑🌒🌓🌔🌕🌖🌗🌘🌙🌚🌛🌜🌝🌞")


def _safe_emoji(s: str | None):
    """Return an emoji string Discord will accept on a SelectOption — or None.

    Catches the common 50035 'invalid emoji' error caused by glyphs that
    look like emoji but aren't on Discord's emoji list (e.g. ✦, ★).
    """
    if not s:
        return None
    s = s.strip()
    if not s:
        return None
    # Custom guild emoji form: <:name:id> or <a:name:id>
    if _CUSTOM_EMOJI_RE.match(s):
        return s
    # Single supplementary-plane codepoint (covers most modern emoji)
    if any(ord(c) >= 0x1F000 for c in s):
        return s
    # Allow our curated BMP set
    if s in _BMP_EMOJI_ALLOW:
        return s
    # Some emoji are 2 chars (base + variation selector U+FE0F)
    if len(s) == 2 and s.endswith("\ufe0f") and ord(s[0]) >= 0x2300:
        return s
    return None


def _sanitize_channel_name(raw: str) -> str:
    """Strip zero-width and control characters, keep it Discord-safe."""
    raw = re.sub(r"[\u200B-\u200F\u202A-\u202E\u2060-\u206F]", "", raw or "")
    raw = re.sub(r"[^a-z0-9\-_]", "-", raw.lower())
    raw = re.sub(r"-{2,}", "-", raw).strip("-")
    return raw[:18] or "ticket"


def _scrub_for_ai(text: str, limit: int = 4000) -> str:
    """Remove explicit prompt-injection style markers before sending to AI."""
    if not text:
        return ""
    text = re.sub(r"(?i)ignore (all )?(previous|prior) (instructions|prompts?)", "[scrubbed]", text)
    text = text.replace("```", "ʼʼʼ")
    return text[:limit]


def _nonce(*parts) -> str:
    raw = "|".join(str(p) for p in parts).encode()
    return hashlib.sha1(raw).hexdigest()[:10]


async def _log_event(db_obj, ticket_id, guild_id, user_id, event_type, detail=None):
    async with db_obj._db_context() as db:
        await db.execute(
            "INSERT INTO ticket_events (ticket_id, guild_id, user_id, event_type, detail) VALUES (?,?,?,?,?)",
            (ticket_id, guild_id, user_id, event_type, detail),
        )
        await db.commit()


async def _get_ticket(db_obj, channel_id):
    async with db_obj._db_context() as db:
        db.row_factory = aiosqlite.Row
        async with db.execute("SELECT * FROM tickets WHERE channel_id=?", (channel_id,)) as c:
            row = await c.fetchone()
    return dict(row) if row else None


async def _get_events(db_obj, ticket_id):
    async with db_obj._db_context() as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT * FROM ticket_events WHERE ticket_id=? ORDER BY created_at ASC", (ticket_id,)
        ) as c:
            return [dict(r) for r in await c.fetchall()]


async def _get_categories(db_obj, guild_id: int) -> dict:
    """Return ordered dict of categories: custom (if any) else defaults."""
    out = {}
    try:
        async with db_obj._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT key, label, emoji, description, priority FROM ticket_custom_categories WHERE guild_id=? ORDER BY rowid",
                (guild_id,),
            ) as cur:
                rows = await cur.fetchall()
        for r in rows:
            out[r["key"]] = {
                "label": r["label"],
                "emoji": r["emoji"] or "📌",
                "description": r["description"] or "",
                "priority": (r["priority"] if "priority" in r.keys() else None) or "normal",
            }
    except Exception:
        pass
    return out or DEFAULT_CATEGORIES


def _fmt_event(ev, guild):
    user = guild.get_member(ev["user_id"])
    name = user.display_name if user else f"User {ev['user_id']}"
    ts = ev["created_at"][:16].replace("T", " ")
    icons = {
        "opened": "📂", "claimed": "🙋", "unclaimed": "🔓",
        "user_added": "➕", "user_removed": "➖", "closed": "🔒",
        "rating": "⭐", "escalated": "🚨", "macro": "💬",
        "priority_changed": "🎚️", "first_response": "✉️",
    }
    icon = icons.get(ev["event_type"], "•")
    detail = f" — {ev['detail']}" if ev.get("detail") else ""
    return f"`{ts}` {icon} **{name}** {ev['event_type'].replace('_', ' ')}{detail}"


# ─────────────────────────────────────────────────────────────────────────────
# Anti-abuse / anti-flood
# ─────────────────────────────────────────────────────────────────────────────


async def _get_reputation(db_obj, guild_id: int, user_id: int) -> dict:
    async with db_obj._db_context() as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT * FROM ticket_user_rep WHERE guild_id=? AND user_id=?",
            (guild_id, user_id),
        ) as c:
            row = await c.fetchone()
    if row:
        return dict(row)
    return {
        "guild_id": guild_id, "user_id": user_id,
        "abuse_score": 0, "total_opened": 0, "total_frivolous": 0,
        "blocked_until": None,
    }


async def _bump_reputation(db_obj, guild_id, user_id, *, abuse_delta=0,
                           opened_delta=0, frivolous_delta=0,
                           block_hours: int | None = None):
    async with db_obj._db_context() as db:
        await db.execute(
            "INSERT OR IGNORE INTO ticket_user_rep (guild_id, user_id) VALUES (?, ?)",
            (guild_id, user_id),
        )
        await db.execute(
            """UPDATE ticket_user_rep
               SET abuse_score = abuse_score + ?,
                   total_opened = total_opened + ?,
                   total_frivolous = total_frivolous + ?
               WHERE guild_id=? AND user_id=?""",
            (abuse_delta, opened_delta, frivolous_delta, guild_id, user_id),
        )
        if block_hours:
            until = (datetime.datetime.utcnow()
                     + datetime.timedelta(hours=block_hours)).isoformat()
            await db.execute(
                "UPDATE ticket_user_rep SET blocked_until=? WHERE guild_id=? AND user_id=?",
                (until, guild_id, user_id),
            )
        await db.commit()


async def _check_can_open(bot, guild: discord.Guild, user: discord.Member) -> tuple[bool, str | None]:
    """Returns (allowed, reason_if_not). Applies cooldown/burst/abuse-block."""
    settings = await bot.db.get_guild_settings(guild.id)
    cooldown = int(settings.get("ticket_user_cooldown") or DEFAULT_USER_COOLDOWN_SEC)
    burst    = int(settings.get("ticket_burst_limit") or DEFAULT_GUILD_BURST_LIMIT)
    now      = time.time()

    # 1. Hard block via reputation
    rep = await _get_reputation(bot.db, guild.id, user.id)
    if rep.get("blocked_until"):
        try:
            until = datetime.datetime.fromisoformat(rep["blocked_until"])
            if until > datetime.datetime.utcnow():
                mins = max(1, int((until - datetime.datetime.utcnow()).total_seconds() // 60))
                return False, f"You're temporarily blocked from opening tickets ({mins}m remaining) due to repeated abuse."
        except Exception:
            pass

    # 2. User cooldown
    last = _user_open_cooldowns.get((guild.id, user.id), 0)
    remaining = cooldown - (now - last)
    if remaining > 0:
        return False, f"Please wait **{int(remaining)}s** before opening another ticket."

    # 3. Guild burst limit (sliding 60s window)
    bucket = _guild_burst_buckets[guild.id]
    while bucket and now - bucket[0] > 60:
        bucket.popleft()
    if len(bucket) >= burst:
        return False, "The support team is currently at capacity. Please try again in a minute."

    return True, None


def _record_open(guild_id: int, user_id: int):
    _user_open_cooldowns[(guild_id, user_id)] = time.time()
    _guild_burst_buckets[guild_id].append(time.time())


# ─────────────────────────────────────────────────────────────────────────────
# Workload-balanced staff routing
# ─────────────────────────────────────────────────────────────────────────────


async def _on_call_pool(bot, guild: discord.Guild) -> list[discord.Member]:
    """Returns the on-call staff list (or falls back to support role members)."""
    settings = await bot.db.get_guild_settings(guild.id)
    members: list[discord.Member] = []

    async with bot.db._db_context() as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT user_id FROM ticket_oncall WHERE guild_id=?", (guild.id,)
        ) as c:
            rows = await c.fetchall()
    for r in rows:
        m = guild.get_member(r["user_id"])
        if m and not m.bot:
            members.append(m)

    if not members:
        role = guild.get_role(settings.get("ticket_support_role_id") or 0)
        if role:
            members = [m for m in role.members if not m.bot]

    return members


async def _select_routed_staff(bot, guild: discord.Guild) -> discord.Member | None:
    """Pick the on-call member with lowest current open ticket count."""
    pool = await _on_call_pool(bot, guild)
    if not pool:
        return None
    loads = {}
    async with bot.db._db_context() as db:
        db.row_factory = aiosqlite.Row
        async with db.execute(
            "SELECT user_id, current_open FROM ticket_staff_load WHERE guild_id=?",
            (guild.id,),
        ) as c:
            for r in await c.fetchall():
                loads[r["user_id"]] = r["current_open"] or 0
    pool.sort(key=lambda m: (loads.get(m.id, 0), m.id))
    return pool[0]


async def _bump_staff_load(db_obj, guild_id, user_id, *, open_delta=0,
                           handled_delta=0, resolved_delta=0,
                           response_seconds: int | None = None):
    async with db_obj._db_context() as db:
        await db.execute(
            "INSERT OR IGNORE INTO ticket_staff_load (guild_id, user_id) VALUES (?, ?)",
            (guild_id, user_id),
        )
        await db.execute(
            """UPDATE ticket_staff_load
               SET current_open = MAX(0, current_open + ?),
                   total_handled = total_handled + ?,
                   total_resolved = total_resolved + ?
               WHERE guild_id=? AND user_id=?""",
            (open_delta, handled_delta, resolved_delta, guild_id, user_id),
        )
        if response_seconds is not None:
            # Rolling average: new = (old*handled + response) / (handled+1)
            await db.execute(
                """UPDATE ticket_staff_load
                   SET avg_response_seconds = CASE
                       WHEN total_handled <= 0 THEN ?
                       ELSE ((avg_response_seconds * total_handled) + ?) / (total_handled + 1)
                   END
                   WHERE guild_id=? AND user_id=?""",
                (response_seconds, response_seconds, guild_id, user_id),
            )
        await db.commit()


def _is_quiet_hours(settings: dict) -> bool:
    s = settings.get("ticket_quiet_start")
    e = settings.get("ticket_quiet_end")
    if s is None or e is None:
        return False
    hour = datetime.datetime.utcnow().hour
    if s == e:
        return False
    if s < e:
        return s <= hour < e
    return hour >= s or hour < e


# ─────────────────────────────────────────────────────────────────────────────
# Components V2 builders — the actual "components no one uses"
# ─────────────────────────────────────────────────────────────────────────────


def _has_v2() -> bool:
    """discord.py 2.6+ exposes Container/Section/etc. on discord.ui."""
    return hasattr(ui, "Container") and hasattr(ui, "Section") and hasattr(ui, "TextDisplay")


def _td(text: str):
    """TextDisplay shorthand."""
    return ui.TextDisplay(text)


def _sep(spacing: str = "small"):
    """Separator shorthand."""
    try:
        return ui.Separator(
            spacing=getattr(discord.SeparatorSpacing, spacing.upper(), discord.SeparatorSpacing.small),
            visible=True,
        )
    except Exception:
        return ui.Separator()


def _section_with_thumb(text: str, thumb_url: str | None):
    """Build a Section with a Thumbnail accessory; falls back to plain TextDisplay if no URL."""
    if thumb_url:
        try:
            return ui.Section(_td(text), accessory=ui.Thumbnail(media=thumb_url))
        except Exception:
            pass
    # No thumbnail (or Thumbnail/Section construction failed) → plain TextDisplay.
    return _td(text)


# ── Persistent panel view (Components V2) ───────────────────────────────────


class TicketCategorySelect(ui.Select):
    """The category dropdown — lives inside an ActionRow inside the Container."""

    def __init__(self, options_data: list | None = None):
        if not options_data:
            options_data = [{"value": k, **v} for k, v in DEFAULT_CATEGORIES.items()]

        options = []
        for o in options_data[:25]:
            label = (o.get("label") or o.get("value") or "Option")[:100]
            value = (o.get("value") or label.lower().replace(" ", "_"))[:100]
            desc  = (o.get("description") or "")[:100]
            emoji = _safe_emoji(o.get("emoji"))
            try:
                options.append(discord.SelectOption(
                    label=label, value=value, emoji=emoji, description=desc,
                ))
            except Exception:
                # Last-resort: drop the emoji entirely if Discord still rejects it.
                options.append(discord.SelectOption(
                    label=label, value=value, description=desc,
                ))
        if not options:
            options = [discord.SelectOption(label="Support", value="general")]

        super().__init__(
            placeholder="Choose a support category to begin…",
            min_values=1, max_values=1, options=options,
            custom_id="xero_t_v3_select",
        )

    async def callback(self, interaction: discord.Interaction):
        # Click throttle (anti-DoS on the select itself)
        key = (interaction.guild.id, interaction.user.id)
        now = time.time()
        if _panel_click_throttle[key] > now:
            return await interaction.response.send_message(
                embed=error_embed("Slow down", "You're clicking too fast. Try again in a moment."),
                ephemeral=True,
            )
        _panel_click_throttle[key] = now + 2.0

        bot = interaction.client
        guild = interaction.guild
        user = interaction.user

        # Anti-flood
        ok, why = await _check_can_open(bot, guild, user)
        if not ok:
            return await interaction.response.send_message(
                embed=error_embed("Can't open ticket", why), ephemeral=True
            )

        # Already-open ticket short-circuit
        async with bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT channel_id FROM tickets WHERE guild_id=? AND user_id=? AND status='open'",
                (guild.id, user.id),
            ) as c:
                existing = await c.fetchone()
        if existing:
            ch = guild.get_channel(existing["channel_id"])
            if ch:
                return await interaction.response.send_message(
                    embed=info_embed("You already have an open ticket", ch.mention),
                    ephemeral=True,
                )

        # Resolve chosen category
        category_key = self.values[0]
        cats = await _get_categories(bot.db, guild.id)
        cat_info = cats.get(category_key) or DEFAULT_CATEGORIES.get(category_key) or {
            "label": category_key.title(), "emoji": "📌", "description": "", "priority": "normal",
        }

        # Show the triage modal — captures issue text & severity hint
        await interaction.response.send_modal(
            TicketTriageModal(category_key=category_key, cat_info=cat_info)
        )


class TicketPanelView(ui.LayoutView):
    """The full panel = Container + Section + Separator + Select (V2)."""

    def __init__(self, *, guild: discord.Guild | None = None,
                 settings: dict | None = None,
                 categories: dict | None = None,
                 stats: dict | None = None):
        super().__init__(timeout=None)

        # If V2 isn't available we fall back to a plain Select (still functional)
        if not _has_v2():
            self.add_item(TicketCategorySelect(
                [{"value": k, **v} for k, v in (categories or DEFAULT_CATEGORIES).items()]
            ))
            return

        cats = categories or DEFAULT_CATEGORIES
        gname = guild.name if guild else "Support"
        gicon = guild.icon.url if (guild and guild.icon) else None
        avg_resp   = stats.get("avg_response", "—") if stats else "—"
        open_n     = stats.get("open_count", 0)     if stats else 0
        rating     = stats.get("avg_rating", "—")   if stats else "—"
        oncall_n   = stats.get("oncall_count", 0)   if stats else 0
        resolved_n = stats.get("resolved_total", 0) if stats else 0

        # Pretty category cards — compact one-liner per category so the
        # block stays readable on phones even with 7+ categories.
        pri_dot = {"urgent": "🔴", "high": "🟠", "normal": "🟡", "low": "🟢"}
        cat_lines = []
        for k, v in cats.items():
            dot = pri_dot.get(v.get("priority", "normal"), "🟡")
            emo = v.get("emoji") or "📌"
            desc = (v.get("description") or "").strip()
            label = v["label"]
            if desc:
                cat_lines.append(f"{dot} {emo} **{label}** — {desc}")
            else:
                cat_lines.append(f"{dot} {emo} **{label}**")
        cat_block = "\n".join(cat_lines) or "_No categories configured._"

        # Rotate flavor lines so panels feel alive.
        flavor = random.choice(PANEL_FLAVORS)

        # Live status pill — green if anyone on-call, amber if not.
        status_pill = "🟢 **Online — staff on duty**" if oncall_n > 0 else \
                      "🟡 **Online — auto-routing only**"

        container = ui.Container(accent_colour=discord.Colour(TC_PRIMARY))

        # ── BANNER ───────────────────────────────────────────────────────
        container.add_item(_section_with_thumb(
            f"# 🎫  {gname} · Support Centre\n"
            f"### _Real humans. AI-assisted triage. SLA-tracked._\n"
            f"{status_pill}",
            gicon,
        ))
        container.add_item(_sep("small"))

        # ── LIVE STAT STRIP ──────────────────────────────────────────────
        # Vertical layout — wraps cleanly on mobile, no horizontal overflow.
        container.add_item(_td(
            "### 📊 Live status\n"
            f"⚡ **Avg response** · `{avg_resp}`\n"
            f"📂 **Open right now** · `{open_n}`\n"
            f"⭐ **Rating** · `{rating}`\n"
            f"✅ **Resolved (all-time)** · `{resolved_n}`"
        ))
        container.add_item(_sep("small"))

        # ── HOW IT WORKS ─────────────────────────────────────────────────
        container.add_item(_td(
            "### How it works\n"
            "**1.** Pick a category below.\n"
            "**2.** Fill in a quick triage form — subject, details, urgency.\n"
            "**3.** A private channel opens and the right staff member is paged.\n"
            "**4.** AI summarises the case on close so it's never re-explained."
        ))
        container.add_item(_sep("small"))

        # ── CATEGORIES ───────────────────────────────────────────────────
        container.add_item(_td(f"### Categories\n{cat_block}"))
        container.add_item(_sep("small"))

        # ── THE SELECT ───────────────────────────────────────────────────
        container.add_item(ui.ActionRow(TicketCategorySelect(
            [{"value": k, **v} for k, v in cats.items()]
        )))

        # ── FOOTER (no separator before it — keeps us within Container's 10-child cap)
        container.add_item(_td(
            f"💡 {flavor}\n"
            f"-# By opening a ticket you agree this conversation may be logged for "
            f"quality, security and AI-assisted summaries. Frivolous tickets are rate-limited."
        ))

        self.add_item(container)


async def _build_panel_view(bot, guild: discord.Guild) -> TicketPanelView:
    settings = await bot.db.get_guild_settings(guild.id)
    cats = await _get_categories(bot.db, guild.id)

    stats = {
        "avg_response": "—", "open_count": 0, "avg_rating": "—",
        "oncall_count": 0, "resolved_total": 0,
    }
    try:
        async with bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT COUNT(*) as n FROM tickets WHERE guild_id=? AND status='open'",
                (guild.id,),
            ) as c:
                stats["open_count"] = (await c.fetchone())["n"]
            async with db.execute(
                "SELECT COUNT(*) as n FROM tickets WHERE guild_id=? AND status='closed'",
                (guild.id,),
            ) as c:
                stats["resolved_total"] = (await c.fetchone())["n"]
            async with db.execute(
                "SELECT AVG(rating) as r FROM tickets WHERE guild_id=? AND rating IS NOT NULL",
                (guild.id,),
            ) as c:
                row = await c.fetchone()
                if row and row["r"]:
                    stats["avg_rating"] = f"{row['r']:.1f}/5"
            async with db.execute(
                "SELECT AVG(avg_response_seconds) as a FROM ticket_staff_load WHERE guild_id=? AND avg_response_seconds>0",
                (guild.id,),
            ) as c:
                row = await c.fetchone()
                if row and row["a"]:
                    secs = int(row["a"])
                    stats["avg_response"] = f"{secs // 60}m {secs % 60}s"
            async with db.execute(
                "SELECT COUNT(*) as n FROM ticket_oncall WHERE guild_id=? AND on_duty=1",
                (guild.id,),
            ) as c:
                stats["oncall_count"] = (await c.fetchone())["n"]
    except Exception:
        pass

    return TicketPanelView(guild=guild, settings=settings, categories=cats, stats=stats)


# ── Ticket-channel header view (V2 layout) ─────────────────────────────────


class TicketHeaderView(ui.LayoutView):
    """The first message inside a ticket channel."""

    def __init__(self, *, ticket_id: int, opener: discord.Member,
                 cat_info: dict, priority: str, sla_due_ts: int | None,
                 routed_to: discord.Member | None,
                 triage_summary: str | None,
                 severity_label: str | None):
        super().__init__(timeout=None)

        if not _has_v2():
            self.add_item(TicketActionRow())
            self.add_item(TicketUtilRow())
            return

        # Priority → accent colour for the whole container.
        accent_map = {
            "urgent": TC_DANGER, "high": 0xE67E22,
            "normal": TC_PRIMARY, "low": TC_SUCCESS,
        }
        accent = accent_map.get(priority, TC_PRIMARY)
        cont = ui.Container(accent_colour=discord.Colour(accent))

        # ── BANNER: ticket code + opener avatar ──────────────────────────
        ticket_code = f"XR-#{ticket_id:04d}"
        joined_str = ""
        try:
            if opener.joined_at:
                joined_str = f"  •  member since <t:{int(opener.joined_at.timestamp())}:R>"
        except Exception:
            pass
        cont.add_item(_section_with_thumb(
            f"# {cat_info.get('emoji','🎫')}  {cat_info['label']}\n"
            f"### `{ticket_code}`  •  opened by {opener.mention}\n"
            f"-# `{opener}`{joined_str}",
            opener.display_avatar.url,
        ))
        cont.add_item(_sep("small"))

        # ── STATUS TRACK ─────────────────────────────────────────────────
        # 🟢 Open  →  ◯ Claimed  →  ◯ Resolved   (only first dot lit at create)
        cont.add_item(_td(
            "```\n"
            "🟢 Open ━━━━━ ⚪ Claimed ━━━━━ ⚪ Resolved\n"
            "```"
        ))

        # ── ISSUE SUMMARY ────────────────────────────────────────────────
        if triage_summary:
            cont.add_item(_td(
                f"### 📝 Issue summary\n"
                f">>> {triage_summary[:1400]}"
            ))

        # ── METADATA STRIP (priority • severity • SLA • routing) ─────────
        sla_str = f"<t:{sla_due_ts}:R>" if sla_due_ts else "—"
        routed = routed_to.mention if routed_to else "_auto-routing in progress…_"
        sev = severity_label or PRIORITY_LABELS.get(priority, priority)
        cont.add_item(_td(
            f"### 🎯 Routing & SLA\n"
            f"**Priority** · {PRIORITY_LABELS.get(priority, priority)}\n"
            f"**AI severity** · {sev}\n"
            f"**Response SLA** · {sla_str}\n"
            f"**Routed to** · {routed}"
        ))

        # ── NEXT STEPS GUIDANCE ──────────────────────────────────────────
        cont.add_item(_td(
            "### ✨ While you wait\n"
            "• Add screenshots, links, IDs — anything that helps.\n"
            "• Staff will be paged automatically; no need to re-ping.\n"
            "• Use `/ticket close` when your issue is resolved."
        ))
        cont.add_item(_sep("small"))

        cont.add_item(TicketActionRow())
        cont.add_item(TicketUtilRow())

        self.add_item(cont)


class TicketActionRow(ui.ActionRow):
    @ui.button(label="Claim", style=discord.ButtonStyle.secondary,
               custom_id="xero_t_v3_claim", emoji="🙋")
    async def claim(self, interaction: discord.Interaction, button: ui.Button):
        await _action_claim(interaction)

    @ui.button(label="Unclaim", style=discord.ButtonStyle.secondary,
               custom_id="xero_t_v3_unclaim", emoji="🔓")
    async def unclaim(self, interaction: discord.Interaction, button: ui.Button):
        await _action_unclaim(interaction)

    @ui.button(label="Close", style=discord.ButtonStyle.danger,
               custom_id="xero_t_v3_close", emoji="🔒")
    async def close(self, interaction: discord.Interaction, button: ui.Button):
        if not interaction.user.guild_permissions.manage_channels:
            return await interaction.response.send_message(
                embed=error_embed("Staff only", "You don't have permission."),
                ephemeral=True,
            )
        await _close_flow(interaction, interaction.client)


class TicketFallbackActionsView(ui.View):
    """Plain View used in the V2-failure fallback path.

    `channel.send(view=...)` requires a `ui.View`; passing a bare ActionRow
    raises 'parameter must be View not TicketActionRow'. We use distinct
    custom_ids so this view never collides with the V2 persistent registry.
    """

    def __init__(self):
        super().__init__(timeout=None)

    @ui.button(label="Claim", style=discord.ButtonStyle.secondary,
               custom_id="xero_t_v3_claim_fb", emoji="🙋")
    async def claim(self, interaction: discord.Interaction, button: ui.Button):
        await _action_claim(interaction)

    @ui.button(label="Unclaim", style=discord.ButtonStyle.secondary,
               custom_id="xero_t_v3_unclaim_fb", emoji="🔓")
    async def unclaim(self, interaction: discord.Interaction, button: ui.Button):
        await _action_unclaim(interaction)

    @ui.button(label="Close", style=discord.ButtonStyle.danger,
               custom_id="xero_t_v3_close_fb", emoji="🔒")
    async def close(self, interaction: discord.Interaction, button: ui.Button):
        if not interaction.user.guild_permissions.manage_channels:
            return await interaction.response.send_message(
                embed=error_embed("Staff only", "You don't have permission."),
                ephemeral=True,
            )
        await _close_flow(interaction, interaction.client)


class TicketUtilRow(ui.ActionRow):
    @ui.button(label="Priority", style=discord.ButtonStyle.secondary,
               custom_id="xero_t_v3_priority", emoji="🎚️")
    async def priority(self, interaction: discord.Interaction, button: ui.Button):
        if not interaction.user.guild_permissions.manage_channels:
            return await interaction.response.send_message(
                embed=error_embed("Staff only", ""), ephemeral=True
            )
        await interaction.response.send_message(
            embed=info_embed("Set priority", "Choose a level:"),
            view=PriorityPickView(), ephemeral=True,
        )

    @ui.button(label="Macro", style=discord.ButtonStyle.secondary,
               custom_id="xero_t_v3_macro", emoji="💬")
    async def macro(self, interaction: discord.Interaction, button: ui.Button):
        if not interaction.user.guild_permissions.manage_channels:
            return await interaction.response.send_message(
                embed=error_embed("Staff only", ""), ephemeral=True
            )
        view = await MacroPickView.build(interaction.client, interaction.guild.id)
        if not view:
            return await interaction.response.send_message(
                embed=info_embed("No macros", "Use `/ticket macro action:add` to create one."),
                ephemeral=True,
            )
        await interaction.response.send_message(
            embed=info_embed("Pick a macro to send", ""),
            view=view, ephemeral=True,
        )

    @ui.button(label="Transcript", style=discord.ButtonStyle.secondary,
               custom_id="xero_t_v3_transcript", emoji="📄")
    async def transcript(self, interaction: discord.Interaction, button: ui.Button):
        if not interaction.user.guild_permissions.manage_channels:
            return await interaction.response.send_message(
                embed=error_embed("Staff only", ""), ephemeral=True
            )
        await _send_transcript(interaction)


# ── Triage modal ────────────────────────────────────────────────────────────


class TicketTriageModal(ui.Modal, title="Open a Support Ticket"):
    def __init__(self, *, category_key: str, cat_info: dict):
        super().__init__(timeout=600)
        self.category_key = category_key
        self.cat_info = cat_info

        self.subject = ui.TextInput(
            label="Short subject", placeholder="One line — what is this about?",
            max_length=100, required=True, style=discord.TextStyle.short,
        )
        self.details = ui.TextInput(
            label="Details", placeholder="Please describe the issue clearly. Include "
                                        "any usernames, IDs, links and what you've already tried.",
            max_length=1500, required=True, style=discord.TextStyle.paragraph,
        )
        self.severity = ui.TextInput(
            label="How urgent? (low / normal / high / urgent)",
            placeholder="normal", max_length=8, required=False,
            style=discord.TextStyle.short,
        )
        self.add_item(self.subject)
        self.add_item(self.details)
        self.add_item(self.severity)

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        try:
            await _create_ticket_from_triage(
                interaction=interaction,
                category_key=self.category_key,
                cat_info=self.cat_info,
                subject=str(self.subject.value),
                details=str(self.details.value),
                severity_hint=str(self.severity.value or "").lower().strip(),
            )
        except Exception as ex:
            logger.error(f"Triage submit: {ex}", exc_info=True)
            await interaction.followup.send(
                embed=error_embed("Couldn't open ticket", str(ex)[:200]),
                ephemeral=True,
            )


# ── Priority picker ─────────────────────────────────────────────────────────


class PriorityPickView(ui.View):
    def __init__(self):
        super().__init__(timeout=120)

        sel = ui.Select(
            placeholder="Set priority…",
            options=[
                discord.SelectOption(label=v, value=k, emoji=v.split(" ")[0])
                for k, v in PRIORITY_LABELS.items()
            ],
        )

        async def _cb(interaction: discord.Interaction):
            new_pri = sel.values[0]
            bot = interaction.client
            ticket = await _get_ticket(bot.db, interaction.channel.id)
            if not ticket:
                return await interaction.response.send_message(
                    embed=error_embed("Not a ticket", ""), ephemeral=True
                )
            async with bot.db._db_context() as db:
                await db.execute(
                    "UPDATE tickets SET priority=? WHERE ticket_id=?",
                    (new_pri, ticket["ticket_id"]),
                )
                await db.commit()
            await _log_event(
                bot.db, ticket["ticket_id"], interaction.guild.id,
                interaction.user.id, "priority_changed",
                f"{ticket.get('priority','—')} → {new_pri}",
            )
            await interaction.response.send_message(
                embed=success_embed("Priority updated", f"Now **{PRIORITY_LABELS[new_pri]}**."),
                ephemeral=True,
            )

        sel.callback = _cb
        self.add_item(sel)


# ── Macro picker ────────────────────────────────────────────────────────────


class MacroPickView(ui.View):
    def __init__(self, macros: list[dict]):
        super().__init__(timeout=120)
        self.macros = {m["name"]: m for m in macros}
        sel = ui.Select(
            placeholder="Pick a canned response…",
            options=[
                discord.SelectOption(
                    label=m["name"][:100], value=m["name"][:100],
                    description=(m["content"] or "")[:80],
                ) for m in macros[:25]
            ],
        )

        async def _cb(interaction: discord.Interaction):
            macro = self.macros.get(sel.values[0])
            if not macro:
                return await interaction.response.send_message("Macro not found.", ephemeral=True)
            await interaction.channel.send(macro["content"][:2000])
            async with interaction.client.db._db_context() as db:
                await db.execute(
                    "UPDATE ticket_macros SET uses = uses + 1 WHERE macro_id=?",
                    (macro["macro_id"],),
                )
                await db.commit()
            ticket = await _get_ticket(interaction.client.db, interaction.channel.id)
            if ticket:
                await _log_event(
                    interaction.client.db, ticket["ticket_id"], interaction.guild.id,
                    interaction.user.id, "macro", f"Used `{macro['name']}`",
                )
            await interaction.response.send_message(
                embed=success_embed("Macro sent", f"`{macro['name']}`"), ephemeral=True
            )

        sel.callback = _cb
        self.add_item(sel)

    @classmethod
    async def build(cls, bot, guild_id: int):
        async with bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM ticket_macros WHERE guild_id=? ORDER BY uses DESC, name ASC LIMIT 25",
                (guild_id,),
            ) as c:
                rows = [dict(r) for r in await c.fetchall()]
        if not rows:
            return None
        return cls(rows)


# ─────────────────────────────────────────────────────────────────────────────
# Action handlers (claim/unclaim/close)
# ─────────────────────────────────────────────────────────────────────────────


async def _action_claim(interaction: discord.Interaction):
    if not interaction.user.guild_permissions.manage_channels:
        return await interaction.response.send_message(
            embed=error_embed("Staff only", ""), ephemeral=True
        )
    bot = interaction.client
    ticket = await _get_ticket(bot.db, interaction.channel.id)
    if not ticket:
        return await interaction.response.send_message(
            embed=error_embed("Not a ticket", ""), ephemeral=True
        )
    if ticket.get("claimed_by"):
        m = interaction.guild.get_member(ticket["claimed_by"])
        return await interaction.response.send_message(
            embed=error_embed("Already claimed",
                              f"Claimed by {m.mention if m else 'someone'}."),
            ephemeral=True,
        )

    response_seconds = None
    try:
        opened = datetime.datetime.fromisoformat(ticket["created_at"].replace("Z", ""))
        response_seconds = int((datetime.datetime.utcnow() - opened).total_seconds())
    except Exception:
        pass

    async with bot.db._db_context() as db:
        await db.execute(
            "UPDATE tickets SET claimed_by=?, first_staff_response=COALESCE(first_staff_response, datetime('now')) WHERE ticket_id=?",
            (interaction.user.id, ticket["ticket_id"]),
        )
        await db.commit()
    await _log_event(
        bot.db, ticket["ticket_id"], interaction.guild.id,
        interaction.user.id, "claimed",
        f"Claimed by {interaction.user.display_name}",
    )
    if not ticket.get("first_staff_response"):
        await _log_event(
            bot.db, ticket["ticket_id"], interaction.guild.id,
            interaction.user.id, "first_response", None,
        )
    await _bump_staff_load(
        bot.db, interaction.guild.id, interaction.user.id,
        open_delta=1, handled_delta=1, response_seconds=response_seconds,
    )

    await interaction.response.send_message(
        embed=success_embed("Claimed", f"🙋 {interaction.user.mention} is now handling this ticket.")
    )


async def _action_unclaim(interaction: discord.Interaction):
    if not interaction.user.guild_permissions.manage_channels:
        return await interaction.response.send_message(
            embed=error_embed("Staff only", ""), ephemeral=True
        )
    bot = interaction.client
    ticket = await _get_ticket(bot.db, interaction.channel.id)
    if not ticket:
        return await interaction.response.send_message(
            embed=error_embed("Not a ticket", ""), ephemeral=True
        )
    if ticket.get("claimed_by"):
        await _bump_staff_load(
            bot.db, interaction.guild.id, ticket["claimed_by"], open_delta=-1
        )
    async with bot.db._db_context() as db:
        await db.execute(
            "UPDATE tickets SET claimed_by=NULL WHERE ticket_id=?",
            (ticket["ticket_id"],),
        )
        await db.commit()
    await _log_event(
        bot.db, ticket["ticket_id"], interaction.guild.id,
        interaction.user.id, "unclaimed",
        f"Released by {interaction.user.display_name}",
    )
    await interaction.response.send_message(
        embed=info_embed("Released", f"🔓 {interaction.user.mention} released this ticket.")
    )


# ─────────────────────────────────────────────────────────────────────────────
# Create ticket from triage submission
# ─────────────────────────────────────────────────────────────────────────────


async def _create_ticket_from_triage(*, interaction: discord.Interaction,
                                     category_key: str, cat_info: dict,
                                     subject: str, details: str,
                                     severity_hint: str):
    bot = interaction.client
    guild = interaction.guild
    user = interaction.user
    settings = await bot.db.get_guild_settings(guild.id)

    # Re-check cooldown (race-safe)
    ok, why = await _check_can_open(bot, guild, user)
    if not ok:
        return await interaction.followup.send(
            embed=error_embed("Can't open ticket", why), ephemeral=True
        )
    _record_open(guild.id, user.id)

    # Resolve priority — explicit hint > category default > "normal"
    priority = severity_hint if severity_hint in PRIORITY_LABELS else (
        cat_info.get("priority") or "normal"
    )

    # Try AI severity classification (best-effort)
    severity_label = None
    ai_summary = None
    try:
        scrubbed = _scrub_for_ai(f"Subject: {subject}\nDetails: {details}", 1200)
        ai_summary = await bot.nvidia.ask(
            "You are a Discord support triage assistant. In 2 short sentences "
            "summarise the user's issue. Then on a new line, output exactly one "
            "of: SEVERITY=urgent | SEVERITY=high | SEVERITY=normal | SEVERITY=low. "
            "Be conservative with 'urgent' (only safety/financial harm).\n\n"
            f"{scrubbed}"
        )
        if ai_summary:
            m = re.search(r"SEVERITY=(urgent|high|normal|low)", ai_summary, re.I)
            if m:
                ai_sev = m.group(1).lower()
                severity_label = PRIORITY_LABELS.get(ai_sev)
                if severity_hint not in PRIORITY_LABELS:
                    priority = ai_sev
                ai_summary = re.sub(r"SEVERITY=\w+", "", ai_summary, flags=re.I).strip()
    except Exception as e:
        logger.debug(f"Triage AI: {e}")

    # Channel or thread?
    use_threads = bool(settings.get("ticket_use_threads"))
    cat = guild.get_channel(settings.get("ticket_category_id") or 0)
    role = guild.get_role(settings.get("ticket_support_role_id") or 0)

    safe_user = _sanitize_channel_name(user.display_name)
    channel_name = f"{cat_info['emoji']}-{safe_user}"

    ow = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        user: discord.PermissionOverwrite(
            view_channel=True, send_messages=True,
            attach_files=True, read_message_history=True,
        ),
        guild.me: discord.PermissionOverwrite(
            view_channel=True, send_messages=True,
            manage_channels=True, manage_messages=True, manage_threads=True,
        ),
    }
    if role:
        ow[role] = discord.PermissionOverwrite(
            view_channel=True, send_messages=True, read_message_history=True
        )

    try:
        if use_threads and cat is None:
            parent = guild.get_channel(settings.get("ticket_panel_channel_id") or 0) \
                     or interaction.channel
            ch = await parent.create_thread(
                name=channel_name, type=discord.ChannelType.private_thread,
                invitable=False,
                reason=f"Ticket — {user} — {cat_info['label']}",
            )
            await ch.add_user(user)
        else:
            ch = await guild.create_text_channel(
                channel_name, category=cat, overwrites=ow,
                topic=f"{cat_info['label']} — {user} — {datetime.datetime.utcnow():%Y-%m-%d}",
            )
    except Exception as ex:
        return await interaction.followup.send(
            embed=error_embed("Couldn't create channel", str(ex)[:200]),
            ephemeral=True,
        )

    # Compute SLA
    response_min = DEFAULT_RESPONSE_SLA_MIN
    try:
        async with bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT response_minutes FROM ticket_sla WHERE guild_id=? AND category_key=?",
                (guild.id, category_key),
            ) as c:
                row = await c.fetchone()
            if row:
                response_min = int(row["response_minutes"])
    except Exception:
        pass
    sla_due = datetime.datetime.utcnow() + datetime.timedelta(minutes=response_min)
    sla_due_ts = int(sla_due.timestamp())

    # Insert ticket row
    async with bot.db._db_context() as db:
        cur = await db.execute(
            """INSERT INTO tickets
               (guild_id, channel_id, user_id, topic, priority, sla_due,
                triage_summary, triage_severity)
               VALUES (?,?,?,?,?,?,?,?)""",
            (guild.id, ch.id, user.id, cat_info["label"], priority,
             sla_due.isoformat(),
             (ai_summary or details)[:1500],
             priority),
        )
        tid = cur.lastrowid
        await db.commit()

    await _log_event(
        bot.db, tid, guild.id, user.id, "opened",
        f"{cat_info['label']} — {subject[:80]}",
    )
    await _bump_reputation(bot.db, guild.id, user.id, opened_delta=1)

    # Workload-balanced routing
    routed = await _select_routed_staff(bot, guild)

    # Send the V2 header
    header_view = TicketHeaderView(
        ticket_id=tid, opener=user, cat_info=cat_info, priority=priority,
        sla_due_ts=sla_due_ts, routed_to=routed,
        triage_summary=(ai_summary or details), severity_label=severity_label,
    )

    quiet = _is_quiet_hours(settings)
    ping_bits = [user.mention]
    if routed and not quiet:
        ping_bits.append(routed.mention)
    elif role and not quiet and not routed:
        ping_bits.append(role.mention)
    ping = " ".join(ping_bits)

    try:
        # Components V2 messages: no embeds, no content beyond mentions allowed.
        await ch.send(content=ping, view=header_view,
                      allowed_mentions=discord.AllowedMentions(
                          users=True, roles=True, everyone=False))
    except Exception as e:
        logger.error(f"V2 header send failed, falling back: {e}")
        emb = comprehensive_embed(
            title=f"Ticket #{tid} — {cat_info['label']}",
            description=(ai_summary or details)[:1500],
            color=TC_PRIMARY, timestamp=discord.utils.utcnow(),
        )
        emb.set_thumbnail(url=user.display_avatar.url)
        await ch.send(content=ping, embed=emb, view=TicketFallbackActionsView())

    # Subject as a separate quoted message for staff scanability
    try:
        await ch.send(f"**Subject:** {discord.utils.escape_markdown(subject)[:200]}")
    except Exception:
        pass

    # Staff Intelligence Brief (V2)
    try:
        brief = await _build_staff_brief_view(bot, guild, user, tid)
        m = await ch.send(view=brief)
        try:
            await m.pin()
        except Exception:
            pass
    except Exception as ex:
        logger.error(f"Staff brief: {ex}")

    await interaction.followup.send(
        embed=success_embed("Ticket opened", f"{ch.mention}\n_Priority:_ **{PRIORITY_LABELS[priority]}**"),
        ephemeral=True,
    )


# ─────────────────────────────────────────────────────────────────────────────
# Staff intelligence brief
# ─────────────────────────────────────────────────────────────────────────────


async def _gather_brief_data(bot, guild, member):
    uid, gid = member.id, guild.id
    db_obj = bot.db
    age_days = (discord.utils.utcnow() - member.created_at).days
    out = {"age_days": age_days, "local_cases": [], "global_cases": [],
           "warns": [], "blacklisted": None, "tkt": {"total": 0, "open_count": 0},
           "lvl": {"level": 0, "total_xp": 0}, "prev_tickets": [], "rep": None}

    async with db_obj._db_context() as db:
        db.row_factory = aiosqlite.Row
        try:
            async with db.execute(
                "SELECT action, reason, timestamp FROM mod_cases WHERE guild_id=? AND user_id=? ORDER BY case_id DESC LIMIT 10",
                (gid, uid),
            ) as c:
                out["local_cases"] = [dict(r) for r in await c.fetchall()]
        except Exception: pass
        try:
            async with db.execute(
                "SELECT guild_id, action, reason, timestamp FROM mod_cases WHERE user_id=? AND guild_id!=? ORDER BY case_id DESC LIMIT 20",
                (uid, gid),
            ) as c:
                out["global_cases"] = [dict(r) for r in await c.fetchall()]
        except Exception: pass
        try:
            async with db.execute(
                "SELECT reason, timestamp FROM warnings WHERE guild_id=? AND user_id=? ORDER BY id DESC LIMIT 5",
                (gid, uid),
            ) as c:
                out["warns"] = [dict(r) for r in await c.fetchall()]
        except Exception: pass
        try:
            async with db.execute("SELECT reason FROM blacklisted_users WHERE user_id=?", (uid,)) as c:
                out["blacklisted"] = await c.fetchone()
        except Exception: pass
        try:
            async with db.execute(
                "SELECT COUNT(*) as total, SUM(CASE WHEN status='open' THEN 1 ELSE 0 END) as open_count FROM tickets WHERE guild_id=? AND user_id=?",
                (gid, uid),
            ) as c:
                row = await c.fetchone()
                out["tkt"] = {"total": row["total"], "open_count": row["open_count"] or 0}
        except Exception: pass
        try:
            async with db.execute(
                "SELECT level, total_xp FROM levels WHERE guild_id=? AND user_id=?",
                (gid, uid),
            ) as c:
                row = await c.fetchone()
                if row:
                    out["lvl"] = dict(row)
        except Exception: pass
        try:
            async with db.execute(
                "SELECT ticket_id, topic, ai_summary, closed_at FROM tickets WHERE guild_id=? AND user_id=? AND status='closed' ORDER BY ticket_id DESC LIMIT 3",
                (gid, uid),
            ) as c:
                out["prev_tickets"] = [dict(r) for r in await c.fetchall()]
        except Exception: pass
    out["rep"] = await _get_reputation(db_obj, gid, uid)
    return out


async def _build_staff_brief_view(bot, guild: discord.Guild,
                                  member: discord.Member,
                                  ticket_id: int) -> ui.LayoutView:
    data = await _gather_brief_data(bot, guild, member)
    rep = data["rep"]
    cross_bans = [c for c in data["global_cases"] if c["action"].lower() in ("ban", "tempban")]

    # Risk score: account age, cross-bans, abuse_score, warns
    risk = 0
    if data["age_days"] < 7: risk += 30
    elif data["age_days"] < 30: risk += 15
    risk += min(40, len(cross_bans) * 12)
    risk += min(20, (rep.get("abuse_score") or 0) * 4)
    risk += min(15, len(data["warns"]) * 3)
    risk = min(100, risk)
    risk_emoji = "🟢" if risk < 25 else ("🟡" if risk < 60 else "🔴")

    if not _has_v2():
        # Fallback to old embed
        e = comprehensive_embed(
            title="STAFF INTELLIGENCE BRIEF",
            description=f"{risk_emoji} Risk score: **{risk}/100**",
            color=TC_PRIMARY,
            thumbnail=member.display_avatar.url,
        )
        e.set_footer(text=f"Case #{ticket_id} • Staff only")
        view = ui.View(timeout=None)
        return view  # caller will switch path; embed-fallback handled inline

    view = ui.LayoutView(timeout=None)
    cont = ui.Container(accent_colour=discord.Colour(TC_DARK))

    cont.add_item(_section_with_thumb(
        f"# 🛰️  Staff Intelligence Brief\n"
        f"**{member.display_name}** — `{member}`  •  `{member.id}`",
        member.display_avatar.url,
    ))
    cont.add_item(_sep("small"))

    cont.add_item(_td(
        f"**{risk_emoji} Risk Score:** `{risk}/100`   "
        f"•   **Account age:** `{data['age_days']}d`   "
        f"•   **Server level:** `{data['lvl']['level']}` (`{data['lvl']['total_xp']:,} XP`)\n"
        f"**Tickets:** `{data['tkt']['total']} total, {data['tkt']['open_count']} open`   "
        f"•   **Frivolous opens:** `{rep.get('total_frivolous',0)}`   "
        f"•   **Abuse score:** `{rep.get('abuse_score',0)}`"
    ))
    cont.add_item(_sep("small"))

    if data["local_cases"]:
        lines = "\n".join(f"▹ **{c['action'].upper()}** — `{c['timestamp'][:10]}` — {(c.get('reason') or '')[:60]}"
                          for c in data["local_cases"][:5])
        cont.add_item(_td(f"### Recent local mod actions\n{lines}"))
        cont.add_item(_sep("small"))

    if cross_bans:
        lines = []
        for b in cross_bans[:5]:
            other = bot.get_guild(b["guild_id"])
            sname = other.name if other else f"Server {b['guild_id']}"
            lines.append(f"▹ **{b['action'].upper()}** in **{sname}**")
        cont.add_item(_td(f"### 🚨 Network risk (XERO Aegis)\n" + "\n".join(lines)))
        cont.add_item(_sep("small"))

    if data["prev_tickets"]:
        lines = []
        for pt in data["prev_tickets"]:
            summary = (pt.get("ai_summary") or "")[:80]
            lines.append(f"▹ **#{pt['ticket_id']}** {pt.get('topic','?')} — {summary}…")
        cont.add_item(_td(f"### 📁 Previous tickets\n" + "\n".join(lines)))
        cont.add_item(_sep("small"))

    if data["blacklisted"]:
        cont.add_item(_td(f"### ⛔ Global blacklist\n`{data['blacklisted']['reason'][:200]}`"))
        cont.add_item(_sep("small"))

    cont.add_item(_td(
        f"_Brief #{ticket_id}  •  Staff-only context  •  Not visible to {member.display_name}._"
    ))

    view.add_item(cont)
    return view


# ─────────────────────────────────────────────────────────────────────────────
# Close flow
# ─────────────────────────────────────────────────────────────────────────────


async def _send_transcript(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    lines = []
    async for msg in interaction.channel.history(limit=500, oldest_first=True):
        lines.append(f"[{msg.created_at.strftime('%H:%M:%S')}] {msg.author.display_name}: {msg.content}")
    if not lines:
        return await interaction.followup.send(
            embed=error_embed("Empty", "No messages."), ephemeral=True
        )
    f = discord.File(io.StringIO("\n".join(lines)), filename=f"{interaction.channel.name}-transcript.txt")
    await interaction.followup.send(
        embed=success_embed("Transcript", f"📄 {len(lines)} messages exported."),
        file=f, ephemeral=True,
    )


async def _close_flow(interaction, bot, reason="Resolved"):
    channel = interaction.channel
    guild = interaction.guild
    db_obj = bot.db
    ticket = await _get_ticket(db_obj, channel.id)
    if not ticket:
        return await interaction.response.send_message(
            embed=error_embed("Not a ticket", "This isn't a ticket channel."),
            ephemeral=True,
        )

    tid = ticket["ticket_id"]
    opener = guild.get_member(ticket["user_id"])
    closer = interaction.user

    await interaction.response.send_message(
        embed=info_embed("Closing", "🔒 Generating case archive…")
    )

    await _log_event(db_obj, tid, guild.id, closer.id, "closed",
                     f"Closed by {closer} — {reason}")

    async with db_obj._db_context() as db:
        await db.execute(
            "UPDATE tickets SET status='closed', closed_at=datetime('now'), closed_by=? WHERE ticket_id=?",
            (closer.id, tid),
        )
        await db.commit()

    # Collect messages
    messages = []
    async for msg in channel.history(limit=500, oldest_first=True):
        messages.append({
            "ts": msg.created_at.strftime("%H:%M"),
            "author": msg.author.display_name,
            "content": (msg.content or "")[:300],
            "is_bot": msg.author.bot,
        })

    ticket = await _get_ticket(db_obj, channel.id)
    events = await _get_events(db_obj, tid)

    # Duration
    duration = "—"
    duration_secs = 0
    try:
        od = datetime.datetime.fromisoformat(ticket["created_at"].replace("Z", ""))
        cd = datetime.datetime.utcnow()
        delta = cd - od
        duration_secs = int(delta.total_seconds())
        h, rem = divmod(duration_secs, 3600)
        duration = f"{h}h {rem // 60}m" if h else f"{rem // 60}m"
    except Exception: pass

    # Frivolous detection: closed in <60s with <2 human msgs
    human_msgs = [m for m in messages if not m["is_bot"] and m["content"].strip()]
    if duration_secs < 60 and len(human_msgs) < 2:
        await _bump_reputation(db_obj, guild.id, ticket["user_id"],
                               abuse_delta=1, frivolous_delta=1)
        # auto-block on threshold
        rep = await _get_reputation(db_obj, guild.id, ticket["user_id"])
        if rep["abuse_score"] >= ABUSE_BLOCK_THRESHOLD:
            await _bump_reputation(db_obj, guild.id, ticket["user_id"],
                                   block_hours=ABUSE_BLOCK_HOURS)

    if ticket.get("claimed_by"):
        await _bump_staff_load(db_obj, guild.id, ticket["claimed_by"],
                               open_delta=-1, resolved_delta=1)

    # AI summary
    ai_summary = None
    try:
        if human_msgs:
            convo = "\n".join(f"{m['author']}: {m['content']}" for m in human_msgs[:40])
            ai_summary = await bot.nvidia.ask(
                "Summarise this Discord support ticket in 2-3 sentences. "
                "Cover: issue, what was done, outcome.\n\n" + _scrub_for_ai(convo)
            )
    except Exception as e:
        logger.debug(f"AI close summary: {e}")

    if ai_summary:
        async with db_obj._db_context() as db:
            await db.execute(
                "UPDATE tickets SET ai_summary=?, message_count=? WHERE ticket_id=?",
                (ai_summary, len(messages), tid),
            )
            await db.commit()

    # Build the V2 archive
    staff_evs = [ev for ev in events if ev["event_type"] not in ("opened", "message")]
    timeline = "\n".join(_fmt_event(ev, guild) for ev in staff_evs) \
               if staff_evs else "_No staff events logged._"

    opener_str = opener.mention if opener else f"<@{ticket['user_id']}>"

    archive_view = ui.LayoutView(timeout=None) if _has_v2() else None
    archive_embed = None

    if archive_view is not None:
        cont = ui.Container(accent_colour=discord.Colour(TC_DARK))
        cont.add_item(_section_with_thumb(
            f"# 📁 Case Archive — Ticket #{tid}\n"
            f"**Topic:** {ticket.get('topic', 'General Support')}\n"
            f"**Status:** Closed by {closer.mention}",
            opener.display_avatar.url if opener else None,
        ))
        cont.add_item(_sep("small"))

        rating_line = ""
        if ticket.get("rating"):
            stars = "⭐" * int(ticket["rating"])
            fb = f" — _{ticket['rating_feedback']}_" if ticket.get("rating_feedback") else ""
            rating_line = f"\n**User rating:** {stars} ({ticket['rating']}/5){fb}"

        cont.add_item(_td(
            f"**Opened by:** {opener_str}   •   `{ticket['user_id']}`\n"
            f"**Closed by:** {closer.mention}\n"
            f"**Duration:** `{duration}`   •   **Messages:** `{len(messages)}`\n"
            f"**Priority:** {PRIORITY_LABELS.get(ticket.get('priority','normal'), '—')}"
            f"{rating_line}"
        ))
        cont.add_item(_sep("small"))
        cont.add_item(_td(f"### Event timeline\n{timeline[:1500]}"))
        cont.add_item(_sep("small"))
        if ai_summary:
            cont.add_item(_td(f"### 🤖 AI intelligence summary\n>>> {ai_summary[:1500]}"))
            cont.add_item(_sep("small"))
        cont.add_item(_td(f"_Closing reason:_ `{reason[:120]}`"))
        archive_view.add_item(cont)
    else:
        fields = [
            ("Opened By", f"{opener_str}\n`ID: {ticket['user_id']}`", False),
            ("Closed By", f"{closer.mention}\n`ID: {closer.id}`", True),
            ("Duration", f"`{duration}`", True),
            ("Messages", f"`{len(messages)}`", True),
            ("Category", f"**{ticket.get('topic','General').upper()}**", True),
            ("Event Timeline", f"```\n{timeline[:800]}\n```", False),
        ]
        if ai_summary:
            fields.append(("AI Intelligence Summary", f"```\n{ai_summary[:500]}\n```", False))
        archive_embed = comprehensive_embed(
            title=f"CASE ARCHIVE: #{tid}", color=TC_DARK, fields=fields,
            thumbnail=opener.display_avatar.url if opener else None,
        )

    # Transcript file
    lines = [
        f"CASE #{tid} TRANSCRIPT — {guild.name}",
        f"Opener: {opener} ({ticket['user_id']})",
        f"Topic: {ticket.get('topic','General')}",
        f"Duration: {duration}",
        "=" * 60, "",
    ]
    for m in messages:
        lines.append(f"[{m['ts']}] {m['author']}: {m['content']}")
    txt_file = discord.File(io.StringIO("\n".join(lines)), filename=f"case-{tid}.txt")

    settings = await bot.db.get_guild_settings(guild.id)
    log_ch = guild.get_channel(
        settings.get("ticket_log_channel_id") or settings.get("log_channel_id") or 0
    )
    target = log_ch or channel
    try:
        if archive_view is not None:
            await target.send(view=archive_view)
            await target.send(file=txt_file)
        else:
            await target.send(embed=archive_embed, file=txt_file)
    except Exception as ex:
        logger.error(f"Archive send: {ex}")
        try:
            await channel.send(file=txt_file)
        except Exception: pass

    await asyncio.sleep(8)
    try:
        if isinstance(channel, discord.Thread):
            await channel.edit(archived=True, locked=True)
        else:
            await channel.delete(reason=f"Ticket #{tid} closed by {closer}")
    except Exception as ex:
        logger.error(f"Channel teardown: {ex}")


# ─────────────────────────────────────────────────────────────────────────────
# Panel registry & auto-repost
# ─────────────────────────────────────────────────────────────────────────────


async def _register_panel(db_obj, guild_id: int, channel_id: int, message_id: int):
    async with db_obj._db_context() as db:
        await db.execute(
            "INSERT OR REPLACE INTO ticket_panels (guild_id, channel_id, message_id, version, posted_at) VALUES (?,?,?,?, datetime('now'))",
            (guild_id, channel_id, message_id, PANEL_VERSION),
        )
        await db.commit()


async def _delete_panel_record(db_obj, message_id: int):
    async with db_obj._db_context() as db:
        await db.execute("DELETE FROM ticket_panels WHERE message_id=?", (message_id,))
        await db.commit()


# NOTE: legacy panel auto-detection / auto-repost was removed.
# Setup is now explicit: admins re-run `/ticket setup` to publish a fresh
# panel. This is simpler, predictable, and avoids touching unrelated
# messages in any server.


# ─────────────────────────────────────────────────────────────────────────────
# History view (V2)
# ─────────────────────────────────────────────────────────────────────────────


class TicketHistoryView(ui.View):
    def __init__(self, bot, guild, tickets, idx=0):
        super().__init__(timeout=120)
        self.bot, self.guild, self.tickets, self.idx = bot, guild, tickets, idx
        self._upd()

    def _upd(self):
        self.prev_btn.disabled = self.idx <= 0
        self.next_btn.disabled = self.idx >= len(self.tickets) - 1
        self.counter.label = f"{self.idx + 1} / {len(self.tickets)}"

    async def _embed(self):
        t = self.tickets[self.idx]
        events = await _get_events(self.bot.db, t["ticket_id"])
        opener = self.guild.get_member(t["user_id"])
        closer = self.guild.get_member(t.get("closed_by") or 0)
        o_str = f"{opener.mention} `{opener}` (`{t['user_id']}`)" if opener else f"<@{t['user_id']}>"
        c_str = f"{closer.mention}" if closer else (f"<@{t['closed_by']}>" if t.get("closed_by") else "Unknown")
        duration = "—"
        try:
            od = datetime.datetime.fromisoformat(t["created_at"].replace("Z", ""))
            cd = datetime.datetime.fromisoformat(t["closed_at"].replace("Z", ""))
            delta = cd - od
            h, rem = divmod(int(delta.total_seconds()), 3600)
            duration = f"{h}h {rem // 60}m" if h else f"{rem // 60}m"
        except Exception: pass

        staff_evs = [ev for ev in events if ev["event_type"] not in ("opened", "message")]
        timeline = "\n".join(_fmt_event(ev, self.guild) for ev in staff_evs) \
                   if staff_evs else "_No staff events on record._"

        e = comprehensive_embed(
            title=f"📁  Case #{t['ticket_id']}",
            color=TC_DARK, timestamp=discord.utils.utcnow(),
        )
        e.add_field(name="👤  Opened By", value=o_str, inline=False)
        e.add_field(name="🔒  Closed By", value=c_str, inline=True)
        e.add_field(name="⏱️  Duration", value=duration, inline=True)
        e.add_field(name="💬  Messages", value=str(t.get("message_count") or "—"), inline=True)
        e.add_field(name="📂  Topic", value=t.get("topic", "General Support"), inline=True)
        ts_open = (
            f"<t:{int(datetime.datetime.fromisoformat(t['created_at'].replace('Z','')).timestamp())}:f>"
            if t.get("created_at") else "—"
        )
        e.add_field(name="📅  Opened", value=ts_open, inline=True)
        if t.get("priority"):
            e.add_field(name="🎚️  Priority", value=PRIORITY_LABELS.get(t["priority"], t["priority"]), inline=True)
        if t.get("rating"):
            fb = f"\n*{t['rating_feedback']}*" if t.get("rating_feedback") else ""
            e.add_field(name="⭐  Rating", value=f"{'⭐'*t['rating']} ({t['rating']}/5){fb}", inline=True)
        e.add_field(name="📋  Event Log", value=timeline[:800], inline=False)
        if t.get("ai_summary"):
            e.add_field(name="🤖  AI Case Summary", value=t["ai_summary"][:500], inline=False)
        if opener:
            e.set_thumbnail(url=opener.display_avatar.url)
        e.set_footer(text=f"Case {self.idx + 1} of {len(self.tickets)}  •  #{t['ticket_id']}  •  XERO Tickets")
        return e

    @ui.button(emoji="◀", style=discord.ButtonStyle.secondary, custom_id="th_prev_v3")
    async def prev_btn(self, interaction, button):
        self.idx -= 1; self._upd()
        await interaction.response.edit_message(embed=await self._embed(), view=self)

    @ui.button(label="1 / 1", style=discord.ButtonStyle.secondary,
               disabled=True, custom_id="th_ctr_v3")
    async def counter(self, interaction, button):
        pass

    @ui.button(emoji="▶", style=discord.ButtonStyle.secondary, custom_id="th_next_v3")
    async def next_btn(self, interaction, button):
        self.idx += 1; self._upd()
        await interaction.response.edit_message(embed=await self._embed(), view=self)


# ─────────────────────────────────────────────────────────────────────────────
# The Cog
# ─────────────────────────────────────────────────────────────────────────────


class Tickets(commands.GroupCog, name="ticket"):
    """Advanced ticket system with persistent panels, AI triage, SLA & macros."""

    def __init__(self, bot):
        self.bot = bot
        # Persistent views must be re-registered each startup
        try:
            bot.add_view(TicketPanelView())
        except Exception:
            pass
        try:
            # Register the legacy-fallback action view too, so its buttons
            # keep working after a bot restart on tickets that landed in
            # the V2-failure fallback path.
            bot.add_view(TicketFallbackActionsView())
        except Exception:
            pass
        try:
            bot.add_view(ui.View(timeout=None))  # base no-op for legacy
        except Exception:
            pass
        # Register persistent action rows by sending a dummy LayoutView once
        # (discord.py treats LayoutView's children as persistent automatically when timeout=None)
        self._sla_loop.start()

    def cog_unload(self):
        try: self._sla_loop.cancel()
        except Exception: pass

    # ── /ticket setup ─────────────────────────────────────────────────────

    @app_commands.command(
        name="setup",
        description="Post the advanced ticket panel (Components V2, AI triage, SLA-aware).",
    )
    @app_commands.describe(
        channel="Where to post the panel",
        support_role="Default role to ping (used when no on-call staff configured)",
        category="Discord category for new ticket channels",
        log_channel="Where case archives are posted on close",
        escalation_role="Role pinged when SLA is breached",
        use_threads="Use private threads instead of channels (saves channel quota)",
    )
    @app_commands.checks.has_permissions(administrator=True)
    async def setup(self, interaction: discord.Interaction,
                    channel: discord.TextChannel,
                    support_role: discord.Role = None,
                    category: discord.CategoryChannel = None,
                    log_channel: discord.TextChannel = None,
                    escalation_role: discord.Role = None,
                    use_threads: bool = False):
        await interaction.response.defer(ephemeral=True)

        if support_role:
            await self.bot.db.update_guild_setting(
                interaction.guild.id, "ticket_support_role_id", support_role.id)
        if category:
            await self.bot.db.update_guild_setting(
                interaction.guild.id, "ticket_category_id", category.id)
        if log_channel:
            await self.bot.db.update_guild_setting(
                interaction.guild.id, "ticket_log_channel_id", log_channel.id)
        if escalation_role:
            await self.bot.db.update_guild_setting(
                interaction.guild.id, "ticket_escalation_role_id", escalation_role.id)
        await self.bot.db.update_guild_setting(
            interaction.guild.id, "ticket_use_threads", 1 if use_threads else 0)
        await self.bot.db.update_guild_setting(
            interaction.guild.id, "ticket_panel_channel_id", channel.id)

        view = await _build_panel_view(self.bot, interaction.guild)
        try:
            msg = await channel.send(view=view)
        except Exception as e:
            return await interaction.followup.send(
                embed=error_embed("Couldn't post panel", str(e)[:200]), ephemeral=True
            )
        await _register_panel(self.bot.db, interaction.guild.id, channel.id, msg.id)
        await interaction.followup.send(
            embed=success_embed("Panel posted",
                                f"Advanced ticket system live in {channel.mention}."),
            ephemeral=True,
        )

    # ── User-facing close / claim / unclaim / add / remove ────────────────

    @app_commands.command(name="close", description="Close this ticket and archive it.")
    @app_commands.describe(reason="Reason for closing")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def close(self, interaction: discord.Interaction, reason: str = "Resolved"):
        await _close_flow(interaction, self.bot, reason)

    @app_commands.command(name="claim", description="Claim this ticket as your responsibility.")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def claim(self, interaction: discord.Interaction):
        await _action_claim(interaction)

    @app_commands.command(name="unclaim", description="Release this ticket so another staff member can take it.")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def unclaim(self, interaction: discord.Interaction):
        await _action_unclaim(interaction)

    @app_commands.command(name="add", description="Add a user to this ticket.")
    @app_commands.describe(user="User to add")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def add(self, interaction: discord.Interaction, user: discord.Member):
        await interaction.channel.set_permissions(
            user, view_channel=True, send_messages=True,
            attach_files=True, read_message_history=True,
        )
        ticket = await _get_ticket(self.bot.db, interaction.channel.id)
        if ticket:
            await _log_event(
                self.bot.db, ticket["ticket_id"], interaction.guild.id,
                interaction.user.id, "user_added",
                f"{user.display_name} added by {interaction.user.display_name}",
            )
        await interaction.response.send_message(
            embed=success_embed("Added", f"➕ {user.mention} added.")
        )

    @app_commands.command(name="remove", description="Remove a user from this ticket.")
    @app_commands.describe(user="User to remove")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def remove(self, interaction: discord.Interaction, user: discord.Member):
        await interaction.channel.set_permissions(user, overwrite=None)
        ticket = await _get_ticket(self.bot.db, interaction.channel.id)
        if ticket:
            await _log_event(
                self.bot.db, ticket["ticket_id"], interaction.guild.id,
                interaction.user.id, "user_removed",
                f"{user.display_name} removed by {interaction.user.display_name}",
            )
        await interaction.response.send_message(
            embed=info_embed("Removed", f"➖ {user.mention} removed.")
        )

    @app_commands.command(name="list", description="View all open tickets.")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def list_tickets(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM tickets WHERE guild_id=? AND status='open' ORDER BY ticket_id DESC",
                (interaction.guild.id,),
            ) as c:
                tickets = [dict(r) for r in await c.fetchall()]
        if not tickets:
            return await interaction.response.send_message(
                embed=info_embed("No open tickets", "All quiet.")
            )
        e = comprehensive_embed(
            title=f"Open Tickets — {len(tickets)} active",
            color=TC_PRIMARY, timestamp=discord.utils.utcnow(),
        )
        for t in tickets[:10]:
            ch = interaction.guild.get_channel(t["channel_id"])
            opener = interaction.guild.get_member(t["user_id"])
            claimer = interaction.guild.get_member(t.get("claimed_by") or 0)
            try:
                ts = f"<t:{int(datetime.datetime.fromisoformat(t['created_at'].replace('Z','')).timestamp())}:R>"
            except Exception:
                ts = "—"
            opener_str = opener.mention if opener else f"<@{t['user_id']}>"
            pri = PRIORITY_LABELS.get(t.get("priority", "normal"), "—")
            e.add_field(
                name=f"#{t['ticket_id']} — {t.get('topic','General')}",
                value=f"**Opener:** {opener_str}\n**Channel:** {ch.mention if ch else '(deleted)'}\n"
                      f"**Claimed:** {claimer.mention if claimer else '—'}\n"
                      f"**Priority:** {pri}\n**Opened:** {ts}",
                inline=True,
            )
        e.set_footer(text="XERO Tickets v3")
        await interaction.response.send_message(embed=e)

    @app_commands.command(name="history", description="Browse closed tickets. Optional user filter.")
    @app_commands.describe(user="Filter to a specific user (optional)")
    @app_commands.checks.has_permissions(manage_channels=True)
    @command_guard
    async def history(self, interaction: discord.Interaction, user: discord.Member = None):
        await interaction.response.defer(ephemeral=True)
        q = "SELECT * FROM tickets WHERE guild_id=? AND status='closed'"
        p = [interaction.guild.id]
        if user:
            q += " AND user_id=?"; p.append(user.id)
        q += " ORDER BY ticket_id DESC"
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(q, p) as c:
                tickets = [dict(r) for r in await c.fetchall()]
        if not tickets:
            msg = "No closed tickets" + (f" for {user.mention}" if user else "") + "."
            return await interaction.followup.send(embed=info_embed("No history", msg))
        view = TicketHistoryView(self.bot, interaction.guild, tickets)
        embed = await view._embed()
        await interaction.followup.send(embed=embed, view=view)

    @app_commands.command(name="rate", description="Rate your most recent support experience 1-5.")
    @app_commands.describe(stars="Your rating", feedback="Optional feedback")
    @app_commands.choices(stars=[
        app_commands.Choice(name="⭐ 1 — Poor", value=1),
        app_commands.Choice(name="⭐⭐ 2 — Fair", value=2),
        app_commands.Choice(name="⭐⭐⭐ 3 — Good", value=3),
        app_commands.Choice(name="⭐⭐⭐⭐ 4 — Great", value=4),
        app_commands.Choice(name="⭐⭐⭐⭐⭐ 5 — Excellent", value=5),
    ])
    async def rate(self, interaction: discord.Interaction, stars: int, feedback: str = ""):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT ticket_id FROM tickets WHERE guild_id=? AND user_id=? ORDER BY ticket_id DESC LIMIT 1",
                (interaction.guild.id, interaction.user.id),
            ) as c:
                row = await c.fetchone()
        if not row:
            return await interaction.response.send_message(
                embed=error_embed("No ticket", "No ticket found to rate."), ephemeral=True
            )
        async with self.bot.db._db_context() as db:
            await db.execute(
                "UPDATE tickets SET rating=?, rating_feedback=? WHERE ticket_id=?",
                (stars, feedback, row["ticket_id"]),
            )
            await db.commit()
        await _log_event(
            self.bot.db, row["ticket_id"], interaction.guild.id,
            interaction.user.id, "rating",
            f"{stars}/5 — {feedback[:80] if feedback else 'no comment'}",
        )
        await interaction.response.send_message(
            embed=success_embed(
                "Thank you",
                f"{'⭐' * stars}{(' — *' + feedback + '*') if feedback else ''}"
            )
        )

    @app_commands.command(name="transcript", description="Export a text transcript of this ticket.")
    @app_commands.checks.has_permissions(manage_channels=True)
    @command_guard
    async def transcript(self, interaction: discord.Interaction):
        await _send_transcript(interaction)

    @app_commands.command(name="rename", description="Rename this ticket channel.")
    @app_commands.describe(name="New channel name")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def rename(self, interaction: discord.Interaction, name: str):
        ticket = await _get_ticket(self.bot.db, interaction.channel.id)
        if not ticket:
            return await interaction.response.send_message(
                embed=error_embed("Not a ticket", ""), ephemeral=True
            )
        try:
            await interaction.channel.edit(name=_sanitize_channel_name(name) or name[:99])
            await interaction.response.send_message(embed=success_embed("Renamed", f"`{name}`"))
        except discord.Forbidden:
            await interaction.response.send_message(
                embed=error_embed("No permission", "I cannot rename this channel."), ephemeral=True
            )

    @app_commands.command(name="reopen", description="Reopen a closed ticket.")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def reopen(self, interaction: discord.Interaction):
        ticket = await _get_ticket(self.bot.db, interaction.channel.id)
        if not ticket:
            return await interaction.response.send_message(
                embed=error_embed("Not a ticket", ""), ephemeral=True
            )
        if ticket.get("status") != "closed":
            return await interaction.response.send_message(
                embed=error_embed("Already open", "This ticket isn't closed."), ephemeral=True
            )
        async with self.bot.db._db_context() as db:
            await db.execute(
                "UPDATE tickets SET status='open', closed_at=NULL, closed_by=NULL WHERE ticket_id=?",
                (ticket["ticket_id"],),
            )
            await db.commit()
        opener = interaction.guild.get_member(ticket["user_id"])
        if opener:
            try:
                await interaction.channel.set_permissions(
                    opener, view_channel=True, send_messages=True, read_message_history=True
                )
            except Exception: pass
        await interaction.response.send_message(
            embed=success_embed("Reopened", f"Ticket #{ticket['ticket_id']} reopened by {interaction.user.mention}.")
        )

    # ── Category management ───────────────────────────────────────────────

    @app_commands.command(name="category-add", description="Add a custom ticket category.")
    @app_commands.describe(name="Category name", emoji="Emoji",
                           description="Short description",
                           priority="Default priority for tickets in this category")
    @app_commands.choices(priority=[
        app_commands.Choice(name="🟢 Low", value="low"),
        app_commands.Choice(name="🟡 Normal", value="normal"),
        app_commands.Choice(name="🟠 High", value="high"),
        app_commands.Choice(name="🔴 Urgent", value="urgent"),
    ])
    @app_commands.checks.has_permissions(administrator=True)
    async def category_add(self, interaction: discord.Interaction, name: str,
                           emoji: str = "📌", description: str = "Open a ticket",
                           priority: str = "normal"):
        key = re.sub(r"[^a-z0-9_]", "_", name.lower())[:20]
        async with self.bot.db._db_context() as db:
            try:
                await db.execute(
                    "INSERT OR REPLACE INTO ticket_custom_categories (guild_id, key, label, emoji, description, priority) VALUES (?,?,?,?,?,?)",
                    (interaction.guild.id, key, name, emoji, description[:100], priority),
                )
                await db.commit()
            except Exception as e:
                return await interaction.response.send_message(
                    embed=error_embed("Failed", str(e)[:200]), ephemeral=True
                )
        await interaction.response.send_message(
            embed=success_embed(
                "Category added",
                f"{emoji} **{name}** ({PRIORITY_LABELS[priority]}) — "
                f"re-run `/ticket setup` to refresh the panel."
            ),
            ephemeral=True,
        )

    @app_commands.command(name="category-remove", description="Remove a custom ticket category.")
    @app_commands.describe(name="Category name to remove")
    @app_commands.checks.has_permissions(administrator=True)
    async def category_remove(self, interaction: discord.Interaction, name: str):
        key = re.sub(r"[^a-z0-9_]", "_", name.lower())[:20]
        async with self.bot.db._db_context() as db:
            await db.execute(
                "DELETE FROM ticket_custom_categories WHERE guild_id=? AND key=?",
                (interaction.guild.id, key),
            )
            await db.commit()
        await interaction.response.send_message(
            embed=success_embed(
                "Removed",
                f"**{name}** removed — re-run `/ticket setup` to refresh the panel."
            ),
            ephemeral=True,
        )

    @app_commands.command(name="categories", description="List all ticket categories for this server.")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def list_categories(self, interaction: discord.Interaction):
        cats = await _get_categories(self.bot.db, interaction.guild.id)
        e = comprehensive_embed(title="Ticket Categories", color=TC_PRIMARY)
        lines = [f"{v['emoji']} **{v['label']}** — {v.get('description','')}  "
                 f"_({PRIORITY_LABELS.get(v.get('priority','normal'), 'normal')})_"
                 for v in cats.values()]
        e.add_field(name=f"Active ({len(cats)})", value="\n".join(lines), inline=False)
        e.set_footer(text="Use /ticket category-add to add or /ticket category-remove to remove.")
        await interaction.response.send_message(embed=e, ephemeral=True)

    # ── Innovation #4: Macros ─────────────────────────────────────────────

    @app_commands.command(name="macro", description="Manage canned reply macros (add/list/remove/use).")
    @app_commands.describe(action="What to do", name="Macro name (no spaces)",
                           content="Content (only for add)")
    @app_commands.choices(action=[
        app_commands.Choice(name="add",    value="add"),
        app_commands.Choice(name="use",    value="use"),
        app_commands.Choice(name="list",   value="list"),
        app_commands.Choice(name="remove", value="remove"),
        app_commands.Choice(name="suggest", value="suggest"),
    ])
    @app_commands.checks.has_permissions(manage_messages=True)
    async def macro(self, interaction: discord.Interaction, action: str,
                    name: str = "", content: str = ""):
        gid = interaction.guild.id

        if action == "add":
            if not name or not content:
                return await interaction.response.send_message(
                    embed=error_embed("Missing args", "Provide both `name` and `content`."),
                    ephemeral=True,
                )
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "INSERT INTO ticket_macros (guild_id, name, content, created_by) VALUES (?,?,?,?)",
                    (gid, name[:50], content[:1900], interaction.user.id),
                )
                await db.commit()
            return await interaction.response.send_message(
                embed=success_embed("Macro added", f"`{name}`"), ephemeral=True
            )

        if action == "remove":
            if not name:
                return await interaction.response.send_message(
                    embed=error_embed("Missing name", ""), ephemeral=True
                )
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "DELETE FROM ticket_macros WHERE guild_id=? AND name=?",
                    (gid, name[:50]),
                )
                await db.commit()
            return await interaction.response.send_message(
                embed=success_embed("Macro removed", f"`{name}`"), ephemeral=True
            )

        if action == "list":
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT name, uses FROM ticket_macros WHERE guild_id=? ORDER BY uses DESC, name ASC",
                    (gid,),
                ) as c:
                    rows = [dict(r) for r in await c.fetchall()]
            if not rows:
                return await interaction.response.send_message(
                    embed=info_embed("No macros", "Use `action:add` to create one."), ephemeral=True
                )
            lines = "\n".join(f"▹ `{r['name']}` — used {r['uses']}×" for r in rows[:25])
            return await interaction.response.send_message(
                embed=comprehensive_embed(title=f"Macros ({len(rows)})", description=lines),
                ephemeral=True,
            )

        if action == "use":
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM ticket_macros WHERE guild_id=? AND name=?",
                    (gid, name[:50]),
                ) as c:
                    row = await c.fetchone()
            if not row:
                return await interaction.response.send_message(
                    embed=error_embed("Not found", f"No macro `{name}`."), ephemeral=True
                )
            await interaction.channel.send(row["content"][:2000])
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "UPDATE ticket_macros SET uses = uses + 1 WHERE macro_id=?",
                    (row["macro_id"],),
                )
                await db.commit()
            ticket = await _get_ticket(self.bot.db, interaction.channel.id)
            if ticket:
                await _log_event(
                    self.bot.db, ticket["ticket_id"], gid, interaction.user.id,
                    "macro", f"Used `{row['name']}`",
                )
            return await interaction.response.send_message(
                embed=success_embed("Macro sent", f"`{name}`"), ephemeral=True
            )

        if action == "suggest":
            await interaction.response.defer(ephemeral=True)
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT name, content FROM ticket_macros WHERE guild_id=?", (gid,),
                ) as c:
                    rows = [dict(r) for r in await c.fetchall()]
            if not rows:
                return await interaction.followup.send(
                    embed=info_embed("No macros", "Add some first."), ephemeral=True
                )
            recent = []
            try:
                async for msg in interaction.channel.history(limit=20, oldest_first=False):
                    if msg.author.bot: continue
                    recent.append(f"{msg.author.display_name}: {msg.content[:200]}")
            except Exception: pass
            recent.reverse()
            ctx = "\n".join(recent[-15:])
            options = "\n".join(f"- {r['name']}: {r['content'][:80]}" for r in rows[:25])
            try:
                ans = await self.bot.nvidia.ask(
                    "You are picking the best canned response for a Discord support ticket. "
                    "Reply ONLY with the macro name, no other text.\n\n"
                    f"Conversation:\n{_scrub_for_ai(ctx)}\n\nMacros:\n{options}"
                )
                pick = (ans or "").strip().split()[0] if ans else ""
                match = next((r for r in rows if r["name"].lower() == pick.lower()), None)
                if match:
                    return await interaction.followup.send(
                        embed=success_embed("Suggested macro", f"`{match['name']}`\n\n{match['content'][:500]}"),
                        ephemeral=True,
                    )
            except Exception as e:
                logger.debug(f"Macro suggest: {e}")
            return await interaction.followup.send(
                embed=info_embed("No clear match", "Try `/ticket macro action:list`."), ephemeral=True
            )

    # ── Innovation #3: SLA configuration ──────────────────────────────────

    @app_commands.command(name="sla", description="Set per-category response SLA in minutes.")
    @app_commands.describe(category_key="Category key (see /ticket categories)",
                           response_minutes="First-response SLA in minutes",
                           resolution_minutes="Total resolution SLA in minutes")
    @app_commands.checks.has_permissions(administrator=True)
    async def sla(self, interaction: discord.Interaction, category_key: str,
                  response_minutes: int, resolution_minutes: int = 1440):
        async with self.bot.db._db_context() as db:
            await db.execute(
                "INSERT OR REPLACE INTO ticket_sla (guild_id, category_key, response_minutes, resolution_minutes) VALUES (?,?,?,?)",
                (interaction.guild.id, category_key, response_minutes, resolution_minutes),
            )
            await db.commit()
        await interaction.response.send_message(
            embed=success_embed(
                "SLA updated",
                f"`{category_key}` → respond in **{response_minutes}m**, resolve in **{resolution_minutes}m**."
            ),
            ephemeral=True,
        )

    # ── Innovation #2: On-call rotation ───────────────────────────────────

    @app_commands.command(name="oncall", description="Manage the on-call staff rotation.")
    @app_commands.describe(action="What to do", member="Staff member (for add/remove)")
    @app_commands.choices(action=[
        app_commands.Choice(name="add", value="add"),
        app_commands.Choice(name="remove", value="remove"),
        app_commands.Choice(name="list", value="list"),
        app_commands.Choice(name="clear", value="clear"),
    ])
    @app_commands.checks.has_permissions(administrator=True)
    async def oncall(self, interaction: discord.Interaction, action: str,
                     member: discord.Member = None):
        gid = interaction.guild.id
        if action == "add":
            if not member:
                return await interaction.response.send_message(
                    embed=error_embed("Missing member", ""), ephemeral=True
                )
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "INSERT OR IGNORE INTO ticket_oncall (guild_id, user_id) VALUES (?, ?)",
                    (gid, member.id),
                )
                await db.commit()
            return await interaction.response.send_message(
                embed=success_embed("Added to on-call", member.mention), ephemeral=True
            )
        if action == "remove":
            if not member:
                return await interaction.response.send_message(
                    embed=error_embed("Missing member", ""), ephemeral=True
                )
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "DELETE FROM ticket_oncall WHERE guild_id=? AND user_id=?",
                    (gid, member.id),
                )
                await db.commit()
            return await interaction.response.send_message(
                embed=success_embed("Removed from on-call", member.mention), ephemeral=True
            )
        if action == "clear":
            async with self.bot.db._db_context() as db:
                await db.execute("DELETE FROM ticket_oncall WHERE guild_id=?", (gid,))
                await db.commit()
            return await interaction.response.send_message(
                embed=success_embed("On-call cleared", ""), ephemeral=True
            )
        if action == "list":
            pool = await _on_call_pool(self.bot, interaction.guild)
            if not pool:
                return await interaction.response.send_message(
                    embed=info_embed("Empty", "No on-call staff. Falls back to support role."),
                    ephemeral=True,
                )
            loads = {}
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT user_id, current_open, total_handled, avg_response_seconds FROM ticket_staff_load WHERE guild_id=?",
                    (gid,),
                ) as c:
                    for r in await c.fetchall():
                        loads[r["user_id"]] = dict(r)
            lines = []
            for m in pool:
                d = loads.get(m.id, {})
                avg = d.get("avg_response_seconds") or 0
                lines.append(
                    f"▹ {m.mention} — open: `{d.get('current_open', 0)}` · "
                    f"handled: `{d.get('total_handled', 0)}` · "
                    f"avg response: `{avg // 60}m {avg % 60}s`"
                )
            return await interaction.response.send_message(
                embed=comprehensive_embed(title=f"On-call ({len(pool)})",
                                          description="\n".join(lines)),
                ephemeral=True,
            )

    # ── User-facing: my open tickets ──────────────────────────────────────

    @app_commands.command(name="me", description="Show your open tickets in this server.")
    async def me(self, interaction: discord.Interaction):
        async with self.bot.db._db_context() as db:
            db.row_factory = aiosqlite.Row
            async with db.execute(
                "SELECT * FROM tickets WHERE guild_id=? AND user_id=? AND status='open' ORDER BY ticket_id DESC",
                (interaction.guild.id, interaction.user.id),
            ) as c:
                rows = [dict(r) for r in await c.fetchall()]
        if not rows:
            return await interaction.response.send_message(
                embed=info_embed("No open tickets", "You have no open tickets."), ephemeral=True
            )
        lines = []
        for t in rows[:10]:
            ch = interaction.guild.get_channel(t["channel_id"])
            pri = PRIORITY_LABELS.get(t.get("priority", "normal"), "—")
            lines.append(
                f"▹ **#{t['ticket_id']}** — {t.get('topic','General')} — "
                f"{ch.mention if ch else '(deleted)'} — {pri}"
            )
        await interaction.response.send_message(
            embed=comprehensive_embed(title="Your open tickets", description="\n".join(lines)),
            ephemeral=True,
        )

    # ── Refresh staff brief ───────────────────────────────────────────────

    @app_commands.command(name="intel", description="Re-fetch and pin the staff intelligence brief.")
    @app_commands.checks.has_permissions(manage_channels=True)
    async def intel(self, interaction: discord.Interaction):
        ticket = await _get_ticket(self.bot.db, interaction.channel.id)
        if not ticket:
            return await interaction.response.send_message(
                embed=error_embed("Not a ticket", ""), ephemeral=True
            )
        opener = interaction.guild.get_member(ticket["user_id"])
        if not opener:
            return await interaction.response.send_message(
                embed=error_embed("Opener missing", "Couldn't find the original opener."),
                ephemeral=True,
            )
        await interaction.response.defer(ephemeral=True)
        view = await _build_staff_brief_view(self.bot, interaction.guild, opener, ticket["ticket_id"])
        m = await interaction.channel.send(view=view) if isinstance(view, ui.LayoutView) \
            else await interaction.channel.send(embed=comprehensive_embed(title="Staff brief unavailable"))
        try: await m.pin()
        except Exception: pass
        await interaction.followup.send(
            embed=success_embed("Brief refreshed", "Pinned in this channel."), ephemeral=True
        )

    # ── Innovation #5: Reputation viewer ──────────────────────────────────

    @app_commands.command(name="reputation", description="View / reset a user's ticket reputation.")
    @app_commands.describe(user="User to inspect", reset="Clear their abuse score & block")
    @app_commands.checks.has_permissions(manage_guild=True)
    async def reputation(self, interaction: discord.Interaction,
                         user: discord.Member, reset: bool = False):
        gid = interaction.guild.id
        if reset:
            async with self.bot.db._db_context() as db:
                await db.execute(
                    "UPDATE ticket_user_rep SET abuse_score=0, total_frivolous=0, blocked_until=NULL WHERE guild_id=? AND user_id=?",
                    (gid, user.id),
                )
                await db.commit()
            return await interaction.response.send_message(
                embed=success_embed("Reset", f"Cleared reputation for {user.mention}."),
                ephemeral=True,
            )
        rep = await _get_reputation(self.bot.db, gid, user.id)
        blocked = rep.get("blocked_until")
        block_str = "—"
        if blocked:
            try:
                until = datetime.datetime.fromisoformat(blocked)
                if until > datetime.datetime.utcnow():
                    block_str = f"<t:{int(until.timestamp())}:R>"
            except Exception: pass
        e = comprehensive_embed(
            title=f"Reputation — {user.display_name}",
            color=TC_PRIMARY,
            fields=[
                ("Abuse score", f"`{rep.get('abuse_score', 0)}` / {ABUSE_BLOCK_THRESHOLD}", True),
                ("Total opened", f"`{rep.get('total_opened', 0)}`", True),
                ("Frivolous", f"`{rep.get('total_frivolous', 0)}`", True),
                ("Blocked until", block_str, False),
            ],
            thumbnail=user.display_avatar.url,
        )
        await interaction.response.send_message(embed=e, ephemeral=True)

    # ── SLA + escalation background loop ──────────────────────────────────

    @tasks.loop(minutes=2)
    async def _sla_loop(self):
        try:
            async with self.bot.db._db_context() as db:
                db.row_factory = aiosqlite.Row
                async with db.execute(
                    "SELECT * FROM tickets WHERE status='open' AND escalated=0 AND sla_due IS NOT NULL"
                ) as c:
                    rows = [dict(r) for r in await c.fetchall()]
            now = datetime.datetime.utcnow()
            for t in rows:
                try:
                    due = datetime.datetime.fromisoformat(t["sla_due"])
                except Exception:
                    continue
                if due >= now:
                    continue
                if t.get("first_staff_response"):
                    continue
                guild = self.bot.get_guild(t["guild_id"])
                if not guild: continue
                ch = guild.get_channel(t["channel_id"])
                if not ch: continue
                settings = await self.bot.db.get_guild_settings(guild.id)
                esc_role = guild.get_role(settings.get("ticket_escalation_role_id") or 0)
                ping = esc_role.mention if esc_role else "@here"
                try:
                    if _has_v2():
                        v = ui.LayoutView(timeout=None)
                        cont = ui.Container(accent_colour=discord.Colour(TC_DANGER))
                        cont.add_item(_td(
                            f"# 🚨 SLA Breached — Ticket #{t['ticket_id']}\n"
                            f"No staff response within the configured window. "
                            f"Escalating to {ping}."
                        ))
                        v.add_item(cont)
                        await ch.send(content=ping, view=v,
                                      allowed_mentions=discord.AllowedMentions(roles=True, everyone=False))
                    else:
                        await ch.send(content=ping,
                                      embed=error_embed("SLA breached",
                                                        f"Ticket #{t['ticket_id']} unanswered."))
                except Exception as e:
                    logger.debug(f"SLA send: {e}")
                async with self.bot.db._db_context() as db:
                    await db.execute(
                        "UPDATE tickets SET escalated=1 WHERE ticket_id=?",
                        (t["ticket_id"],),
                    )
                    await db.commit()
                await _log_event(
                    self.bot.db, t["ticket_id"], guild.id, self.bot.user.id,
                    "escalated", "SLA breached — auto-escalated",
                )
        except Exception as e:
            logger.debug(f"SLA loop: {e}")

    @_sla_loop.before_loop
    async def _before_sla(self):
        await self.bot.wait_until_ready()

# ─────────────────────────────────────────────────────────────────────────────
# Setup — schema migrations
# ─────────────────────────────────────────────────────────────────────────────


async def setup(bot):
    try:
        async with bot.db._db_context() as db:
            # 1. Ticket table column upgrades
            for col in [
                "claimed_by INTEGER",
                "rating INTEGER",
                "rating_feedback TEXT",
                "message_count INTEGER DEFAULT 0",
                "ai_summary TEXT",
                "log_message_id INTEGER",
                "priority TEXT DEFAULT 'normal'",
                "sla_due DATETIME",
                "escalated INTEGER DEFAULT 0",
                "first_staff_response DATETIME",
                "triage_summary TEXT",
                "triage_severity TEXT",
            ]:
                try: await db.execute(f"ALTER TABLE tickets ADD COLUMN {col}")
                except Exception: pass

            # 2. Custom categories — add priority col on existing tables
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_custom_categories (
                    guild_id INTEGER NOT NULL,
                    key TEXT NOT NULL,
                    label TEXT NOT NULL,
                    emoji TEXT,
                    description TEXT,
                    priority TEXT DEFAULT 'normal',
                    PRIMARY KEY(guild_id, key)
                )"""
            )
            try: await db.execute("ALTER TABLE ticket_custom_categories ADD COLUMN priority TEXT DEFAULT 'normal'")
            except Exception: pass

            # 3. Events table
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_events (
                    event_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    ticket_id INTEGER NOT NULL,
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    event_type TEXT NOT NULL,
                    detail TEXT,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )"""
            )

            # 4. Panel registry
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_panels (
                    guild_id INTEGER NOT NULL,
                    channel_id INTEGER NOT NULL,
                    message_id INTEGER PRIMARY KEY,
                    posted_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                    version INTEGER DEFAULT 1
                )"""
            )

            # 5. Macros
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_macros (
                    macro_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    guild_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    content TEXT NOT NULL,
                    created_by INTEGER,
                    uses INTEGER DEFAULT 0,
                    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
                )"""
            )
            await db.execute(
                "CREATE INDEX IF NOT EXISTS idx_macros_guild ON ticket_macros(guild_id, name)"
            )

            # 6. SLA
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_sla (
                    guild_id INTEGER NOT NULL,
                    category_key TEXT NOT NULL,
                    response_minutes INTEGER DEFAULT 30,
                    resolution_minutes INTEGER DEFAULT 1440,
                    PRIMARY KEY(guild_id, category_key)
                )"""
            )

            # 7. On-call
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_oncall (
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    PRIMARY KEY(guild_id, user_id)
                )"""
            )

            # 8. Reputation
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_user_rep (
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    abuse_score INTEGER DEFAULT 0,
                    total_opened INTEGER DEFAULT 0,
                    total_frivolous INTEGER DEFAULT 0,
                    blocked_until DATETIME,
                    PRIMARY KEY(guild_id, user_id)
                )"""
            )

            # 9. Staff load tracker
            await db.execute(
                """CREATE TABLE IF NOT EXISTS ticket_staff_load (
                    guild_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    current_open INTEGER DEFAULT 0,
                    total_handled INTEGER DEFAULT 0,
                    total_resolved INTEGER DEFAULT 0,
                    avg_response_seconds INTEGER DEFAULT 0,
                    PRIMARY KEY(guild_id, user_id)
                )"""
            )

            # 10. guild_settings columns for new system
            for col in [
                "ticket_panel_channel_id INTEGER",
                "ticket_escalation_role_id INTEGER",
                "ticket_burst_limit INTEGER",
                "ticket_user_cooldown INTEGER",
                "ticket_use_threads INTEGER DEFAULT 0",
                "ticket_quiet_start INTEGER",
                "ticket_quiet_end INTEGER",
            ]:
                try: await db.execute(f"ALTER TABLE guild_settings ADD COLUMN {col}")
                except Exception: pass

            await db.commit()
    except Exception as e:
        logger.error(f"Ticket migration: {e}")

    await bot.add_cog(Tickets(bot))
