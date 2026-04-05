"""
XERO Bot — Welcome Card Image Processor
Stores images in SQLite DB (base64) so they survive Railway restarts.
Falls back to filesystem for local dev.
"""
from PIL import Image, ImageDraw, ImageFont, ImageFilter
import io, os, logging, base64, aiosqlite


logger = logging.getLogger("XERO.WelcomeCard")

WELCOME_DIR = "data/welcome_images"
os.makedirs(WELCOME_DIR, exist_ok=True)

CARD_W, CARD_H = 1024, 320

DB_PATH = os.getenv("DB_PATH", "data/xero.db")

FONT_PATHS = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf",
    "/usr/share/fonts/truetype/ubuntu/Ubuntu-B.ttf",
    "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf",
]
FONT_PATHS_REGULAR = [p.replace("Bold","").replace("-B.ttf",".ttf") for p in FONT_PATHS]


def _load_font(size: int, bold: bool = True):
    paths = FONT_PATHS if bold else FONT_PATHS_REGULAR
    for fp in paths:
        if os.path.exists(fp):
            try: return ImageFont.truetype(fp, size)
            except Exception: pass
    return ImageFont.load_default()


def _hex_to_rgba(hex_color: str, alpha: int = 255) -> tuple:
    h = hex_color.lstrip("#")
    if len(h) == 3: h = "".join(c*2 for c in h)
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    return (r, g, b, alpha)


async def _save_to_db(guild_id: int, image_bytes: bytes, db_obj=None):
    """Save image as base64 in DB."""
    b64 = base64.b64encode(image_bytes).decode("utf-8")
    ctx = db_obj._db_context() if db_obj else aiosqlite.connect(DB_PATH)
    async with ctx as db:
        try:
            await db.execute(
                "UPDATE guild_settings SET welcome_card_image_data=? WHERE guild_id=?",
                (b64, guild_id)
            )
            await db.commit()
        except Exception as e:
            logger.debug(f"Failed to save welcome card to DB for guild {guild_id}: {e}")


async def _load_from_db(guild_id: int, db_obj=None) -> bytes | None:
    """Load image bytes from DB. Priority: unified_image_data -> welcome_card_image_data."""
    try:
        ctx = db_obj._db_context() if db_obj else aiosqlite.connect(DB_PATH)
    async with ctx as db:
            db.row_factory = aiosqlite.Row
            try:
                async with db.execute(
                    "SELECT unified_image_data, welcome_card_image_data FROM guild_settings WHERE guild_id=?",
                    (guild_id,)
                ) as c:
                    row = await c.fetchone()
                    if row:
                        # Priority 1: Unified Branding Image
                        if row["unified_image_data"]:
                            return base64.b64decode(row["unified_image_data"])
                        # Priority 2: Legacy Welcome Card Image
                        if row["welcome_card_image_data"]:
                            return base64.b64decode(row["welcome_card_image_data"])
            except Exception:
                pass
    except Exception as e:
        logger.debug(f"DB image load: {e}")
    return None


def _get_base_image_sync(guild_id: int) -> bytes | None:
    """Sync check — reads from filesystem only (for quick exists check)."""
    path = os.path.join(WELCOME_DIR, f"{guild_id}.png")
    if os.path.exists(path):
        with open(path, "rb") as f: return f.read()
    return None


def _get_base_image(guild_id: int) -> bytes | None:
    """Try filesystem first, return bytes if image exists."""
    return _get_base_image_sync(guild_id)


def save_base_image(guild_id: int, image_bytes: bytes) -> str:
    """Save image to filesystem AND schedule DB save."""
    path = os.path.join(WELCOME_DIR, f"{guild_id}.png")
    img = Image.open(io.BytesIO(image_bytes)).convert("RGB")
    img.save(path, "PNG", optimize=True)
    # Also store raw bytes for DB backup
    _save_base_image_bytes[guild_id] = image_bytes
    return path

# Buffer for async DB save
_save_base_image_bytes: dict = {}


async def save_base_image_async(guild_id: int, image_bytes: bytes) -> str:
    """Save image to both filesystem and DB."""
    path = os.path.join(WELCOME_DIR, f"{guild_id}.png")
    img = Image.open(io.BytesIO(image_bytes)).convert("RGB")
    buf = io.BytesIO()
    img.save(buf, "PNG", optimize=True)
    buf.seek(0)
    png_bytes = buf.read()
    # Save to filesystem
    with open(path, "wb") as f: f.write(png_bytes)
    # Save to DB
    await _save_to_db(guild_id, png_bytes)
    logger.info(f"Welcome image saved to DB + filesystem for guild {guild_id}")
    return path


async def get_base_image_async(guild_id: int) -> bytes | None:
    """Get image — filesystem first, then DB fallback."""
    # Try filesystem
    data = _get_base_image_sync(guild_id)
    if data:
        return data
    # Fallback to DB (e.g. after Railway restart)
    data = await _load_from_db(guild_id)
    if data:
        # Restore to filesystem for this session
        path = os.path.join(WELCOME_DIR, f"{guild_id}.png")
        try:
            with open(path, "wb") as f: f.write(data)
            logger.info(f"Restored welcome image from DB for guild {guild_id}")
        except Exception: pass
        return data
    return None


def delete_base_image(guild_id: int):
    path = os.path.join(WELCOME_DIR, f"{guild_id}.png")
    if os.path.exists(path):
        os.remove(path)


def generate_welcome_card(
    guild_id: int,
    member_name: str,
    member_avatar_bytes: bytes | None = None,
    text_color: str = "#FFFFFF",
    text_position: str = "bottom_left",
    show_name: bool = True,
    show_avatar: bool = True,
    show_member_count: bool = True,
    member_count: int = 0,
    server_name: str = "",
    overlay_style: str = "gradient",
    font_size: int = 52,
    custom_text: str = "",
    base_bytes: bytes | None = None,  # pass directly to avoid async issues
) -> bytes | None:
    if base_bytes is None:
        base_bytes = _get_base_image(guild_id)
    if not base_bytes:
        return None
    try:
        base = Image.open(io.BytesIO(base_bytes)).convert("RGBA")
        ow, oh = base.size
        ratio = max(CARD_W / ow, CARD_H / oh)
        nw, nh = int(ow * ratio) + 1, int(oh * ratio) + 1
        base  = base.resize((nw, nh), Image.LANCZOS)
        cx    = (nw - CARD_W) // 2
        cy    = (nh - CARD_H) // 2
        base  = base.crop((cx, cy, cx + CARD_W, cy + CARD_H))
        w, h  = CARD_W, CARD_H

        overlay = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        if overlay_style == "gradient":
            for y in range(h):
                frac  = max(0, (y - h * 0.35) / (h * 0.65))
                alpha = int(190 * (frac ** 1.5))
                for x in range(w):
                    overlay.putpixel((x, y), (0, 0, 0, alpha))
        elif overlay_style == "bar":
            bar_h = 100
            bar   = Image.new("RGBA", (w, bar_h), (0, 0, 0, 170))
            overlay.paste(bar, (0, h - bar_h))
        elif overlay_style == "full":
            overlay = Image.new("RGBA", (w, h), (0, 0, 0, 110))
        base = Image.alpha_composite(base, overlay)
        draw = ImageDraw.Draw(base)

        font_name = _load_font(font_size, bold=True)
        font_sub  = _load_font(max(18, font_size // 2 + 2), bold=False)

        def shadow_text(txt, x, y, fnt, color_hex, layers=3):
            r, g, b, _ = _hex_to_rgba(color_hex)
            for i in range(layers, 0, -1):
                draw.text((x + i, y + i), txt, font=fnt, fill=(0, 0, 0, int(200 / i)))
            draw.text((x, y), txt, font=fnt, fill=(r, g, b, 255))

        AV_SIZE   = 84
        AV_BORDER = 4
        AV_TOTAL  = AV_SIZE + AV_BORDER * 2
        MARGIN    = 24
        TEXT_X    = MARGIN + AV_TOTAL + 14 if show_avatar else MARGIN

        if show_name and member_name:
            name = member_name[:26] + "…" if len(member_name) > 26 else member_name
            nb   = draw.textbbox((0, 0), name, font=font_name)
            nw_, nh_ = nb[2] - nb[0], nb[3] - nb[1]
            pos_map = {
                "bottom_left":   (TEXT_X, h - nh_ - MARGIN - 4),
                "bottom_center": ((w - nw_) // 2, h - nh_ - MARGIN - 4),
                "bottom_right":  (w - nw_ - MARGIN, h - nh_ - MARGIN - 4),
                "center":        (TEXT_X, (h - nh_) // 2),
                "top_left":      (TEXT_X, MARGIN),
            }
            nx, ny = pos_map.get(text_position, (TEXT_X, h - nh_ - MARGIN - 4))
            shadow_text(name, nx, ny, font_name, text_color)

            if custom_text:
                sub = custom_text.replace("{count}", str(member_count)).replace("{server}", server_name)
            elif show_member_count and member_count:
                sub = f"Member #{member_count:,}  •  {server_name}" if server_name else f"Member #{member_count:,}"
            elif server_name:
                sub = f"Welcome to {server_name}"
            else:
                sub = ""

            if sub:
                sb    = draw.textbbox((0, 0), sub, font=font_sub)
                sw_   = sb[2] - sb[0]
                sub_x = nx if text_position in ("bottom_left","center","top_left") else (w - sw_) // 2
                sub_y = ny - (sb[3] - sb[1]) - 6
                shadow_text(sub, sub_x, sub_y, font_sub, "#D8D8D8", layers=2)

        if show_avatar and member_avatar_bytes:
            try:
                av      = Image.open(io.BytesIO(member_avatar_bytes)).convert("RGBA")
                av      = av.resize((AV_SIZE, AV_SIZE), Image.LANCZOS)
                bd      = Image.new("RGBA", (AV_TOTAL, AV_TOTAL), (0, 0, 0, 0))
                bd_draw = ImageDraw.Draw(bd)
                bd_draw.ellipse((0, 0, AV_TOTAL - 1, AV_TOTAL - 1), fill=(255, 255, 255, 255))
                av_mask = Image.new("L", (AV_SIZE, AV_SIZE), 0)
                ImageDraw.Draw(av_mask).ellipse((0, 0, AV_SIZE - 1, AV_SIZE - 1), fill=255)
                av.putalpha(av_mask)
                bd.paste(av, (AV_BORDER, AV_BORDER), av)
                base.paste(bd, (MARGIN, h - AV_TOTAL - MARGIN), bd)
            except Exception as e:
                logger.debug(f"Avatar overlay: {e}")

        out = io.BytesIO()
        base.convert("RGB").save(out, format="PNG", optimize=True)
        return out.getvalue()
    except Exception as e:
        logger.error(f"Welcome card error: {e}")
        return None


async def fetch_avatar(url: str) -> bytes | None:
    try:
        import aiohttp
        async with aiohttp.ClientSession() as s:
            async with s.get(url + "?size=128", timeout=aiohttp.ClientTimeout(total=5)) as r:
                if r.status == 200:
                    return await r.read()
    except Exception:
        pass
    return None
