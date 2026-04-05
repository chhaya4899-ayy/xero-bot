You are continuing development of XERO Bot — a production Discord bot built by Team Flame.
The full codebase is at: https://github.com/kushwork1209-prog/xero-bot

READ THIS ENTIRE DOCUMENT BEFORE TOUCHING ANYTHING.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
CRITICAL RULES — VIOLATING THESE BREAKS THE BOT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. ALWAYS run `python3 -c "import ast; ast.parse(open('file.py').read())"` on EVERY file you edit before committing. If there is a syntax error, fix it. Never push broken code.

2. NEVER touch more than 3 files per task unless you have verified all of them pass syntax check.

3. NEVER use `git push --force` unless you have confirmed your local code is clean and intentionally overriding.

4. DO NOT use `manus.ai` or any other AI service on this repo. The last time it was used, it broke 30+ files simultaneously, destroyed core_admin.py (gutted from 2000 lines to nothing), introduced `await` outside async functions, and created cascading import failures across the entire bot.

5. Before editing any cog, read it FULLY first. Do not assume what's in it.

6. Discord has a hard limit of 100 slash command GROUPS and 25 commands PER GROUP. Check counts with the audit script below before adding commands.

7. Every deferred command MUST have error handling. Use `@command_guard` from `utils/guard.py` on any async command that calls an external API or database. This prevents "thinking forever" bugs.

8. Never add `ephemeral=True` to normal command responses — only error messages and private data (balance, etc.) should be ephemeral.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
TECH STACK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

- Language:       Python 3.11
- Framework:      discord.py 2.7.1
- Database:       SQLite via aiosqlite (single file: xero_bot.db)
- AI:             NVIDIA NIM API — model: meta/llama-3.1-8b-instruct
- Image gen:      Pollinations.ai (free, no key)
- Hosting:        Railway (auto-deploys on git push to main branch)
- Repo:           github.com/kushwork1209-prog/xero-bot

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
ENVIRONMENT VARIABLES (set in Railway dashboard)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

DISCORD_TOKEN          — bot token
MANAGEMENT_GUILD_ID    — staff server ID (1431852658767040535)
NVIDIA_MAIN_KEY        — NVIDIA API key for text AI
NVIDIA_VISION_KEY      — NVIDIA API key for vision AI
NVIDIA_AUDIO_KEY       — NVIDIA API key for audio (can reuse MAIN)
BACKUP_CHANNEL_ID      — Discord channel ID for DB backups (set this!)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
FILE STRUCTURE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

xero-bot/
├── main.py                  ← Bot entry point, cog loading, sync, backup loop
├── database.py              ← All DB table creation and helpers
├── requirements.txt
├── Dockerfile               ← For Railway deployment
├── cogs/                    ← All 45 command cogs
│   ├── events.py            ← ALL Discord events (on_message, on_member_join, etc.)
│   ├── core_admin.py        ← /core + /support — management guild ONLY
│   ├── security.py          ← /security — anti-nuke, raids, quarantine, lockdown
│   ├── automod.py           ← /automod — config only (enforcement is in events.py)
│   ├── verification.py      ← /verify — full verification system v2
│   ├── ai.py                ← /ai — all AI commands
│   ├── economy.py           ← /economy
│   ├── levels.py            ← /levels
│   └── ... (40 more cogs)
└── utils/
    ├── embeds.py            ← All embed factories + XERO color palette
    ├── guard.py             ← @command_guard decorator (prevents thinking forever)
    ├── db_backup.py         ← Discord channel backup system
    ├── nvidia_api.py        ← NVIDIA AI wrapper
    └── welcome_card.py      ← Pillow welcome card generator

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
CURRENT STATE (as of last clean push)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

- 395 total slash commands
- 47 command groups
- 45 cogs loaded
- Zero syntax errors
- Zero import errors
- All commands synced globally + management guild

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
HOW THE BOT WORKS — KEY SYSTEMS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

DATABASE BACKUP:
- Uses BACKUP_CHANNEL_ID env var (set in Railway)
- On startup: scans channel for largest valid JSON backup, restores it
- Every 10 minutes: saves full DB snapshot (all tables) as JSON attachment
- Manual: /core backup-now, /core restore-backup
- This is how settings survive Railway restarts (Railway has ephemeral filesystem)

AUTOMOD:
- Config stored in automod_config table via /automod commands
- ENFORCEMENT happens in events.py → on_message → _run_automod()
- Features: anti-spam (5msg/5s), anti-caps (75%+ caps), mention spam, emoji spam, word filter
- Action can be: delete, warn, timeout (5min), kick

SECURITY:
- Anti-nuke: tracks channel_delete, role_delete, mass_ban, mass_kick per user
  Threshold triggers: strip all roles + 10min timeout + DM all admins
- Raid detection: 10+ joins in 10s → lock all channels → auto-unlock after 10min
- Account age filter: enforced in events.py → on_member_join
- Quarantine: strips roles, adds "Quarantined" role, saves original roles in memory
- Role restore: saves roles on member leave → restores on rejoin
- All security functions in Security cog, called from events.py

MANAGEMENT DASHBOARD:
- /core dashboard — opens an 8-panel Discord UI (ephemeral, management guild only)
- Panels: Stats, Servers, Blacklist, Analytics, Tools, Staff, Incidents, Health
- /core and /support commands are MANAGEMENT GUILD ONLY via guilds=[mguild] in add_cog
- Never use copy_global_to() — it duplicates all global commands into the guild

COMMAND SYNC:
- Happens automatically in setup_hook on startup
- /core sync — force resync from Discord (if commands are missing, run this)
- Global commands take up to 1 hour to appear in all servers
- Management guild commands sync instantly

AI SYSTEM:
- Model: meta/llama-3.1-8b-instruct (fast, good quality)
- Timeout: 25 seconds (set in nvidia_api.py)
- All AI commands use @command_guard to prevent hanging
- Member intelligence: passive skill detection, always-on personality AI

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
AUDIT SCRIPT — RUN THIS BEFORE ANY COMMIT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

python3 -c "
import ast, os, re
from collections import Counter
errors = []; groups = {}; top_lvl = []
for fname in os.listdir('cogs'):
    if not fname.endswith('.py'): continue
    with open(f'cogs/{fname}') as f: c = f.read()
    try:
        ast.parse(c)
        current = None
        for line in c.split('\n'):
            gm = re.search(r'GroupCog, name=\"([^\"]+)\"', line)
            if gm: current = gm.group(1)
            cm = re.search(r'@app_commands\.command\(name=\"([^\"]+)\"', line)
            if cm:
                if current:
                    if current not in groups: groups[current] = []
                    groups[current].append(cm.group(1))
                else: top_lvl.append(cm.group(1))
    except SyntaxError as e: errors.append(f'{fname}:L{e.lineno}:{e.msg}')
for f in ['main.py','database.py','utils/embeds.py','utils/guard.py']:
    with open(f) as fp: c = fp.read()
    try: ast.parse(c)
    except SyntaxError as e: errors.append(f'{f}:L{e.lineno}:{e.msg}')
total  = sum(len(v) for v in groups.values()) + len(top_lvl)
over25 = [(g,len(v)) for g,v in groups.items() if len(v)>25]
dupes  = [n for n,c in Counter(top_lvl).items() if c>1]
slots  = len(groups) + len(set(top_lvl))
print(f'Syntax errors: {errors or \"NONE\"}')
print(f'Commands: {total}  Slots: {slots}/100  Over25: {over25 or \"none\"}  Dupes: {dupes or \"none\"}')
"

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
HOW TO PUSH CHANGES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

git add -A
git commit -m "Description of change"
git push origin main

If rejected (remote has changes you don't have):
git push origin main --force
(Only do this if you are SURE your version is correct and complete)

Railway auto-deploys on every push to main branch.
Check Railway logs to confirm the bot started successfully.
Look for: "✓ XERO ready" in the logs.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
EMBED STYLE GUIDE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Colors (from utils/embeds.py XERO palette):
  XERO.PRIMARY   = 0x00D4FF  (electric blue)
  XERO.SUCCESS   = 0x00FF94  (neon green)
  XERO.ERROR     = 0xFF3B5C  (red)
  XERO.WARNING   = 0xFFB800  (amber)
  XERO.GOLD      = 0xFFD700
  XERO.SECONDARY = 0x7B2FFF  (purple)

Management dashboard palette (core_admin.py):
  D_BLACK = 0x0A0A0A   D_BLUE = 0x89CFF0   D_DARK = 0x1C1C1C

Use existing embed factories:
  success_embed(title, desc)
  error_embed(title, desc)
  info_embed(title, desc)
  comprehensive_embed(title, desc, color, ...)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
KNOWN ISSUES / WHAT STILL NEEDS WORK
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Music commands (/music play etc.) — requires PyNaCl with libsodium
   which is installed via Dockerfile. If music doesn't work, check Railway
   build logs for PyNaCl installation errors.

2. Voice AI (/ai-voice) — requires discord-ext-voice_recv which has no
   stable release. These 4 commands will error. Do not try to fix this
   without a stable package version.

3. psutil — not available on Railway free tier. RAM/CPU stats show N/A.
   All psutil usage is wrapped in try/except — leave it that way.

4. Welcome card images — stored as base64 in DB (welcome_card_image_data
   column) via utils/welcome_card.py. Images survive restarts this way.

5. BACKUP_CHANNEL_ID — must be set in Railway env vars. Without it,
   the backup system is silent (no errors, just no backups).

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
THINGS TO NEVER DO
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

- Never call self.bot.tree.copy_global_to(guild=mguild) — duplicates commands
- Never add await inside a non-async function
- Never import at module level something that requires DB connection
- Never use time.sleep() — always use await asyncio.sleep()
- Never store secrets in code — use env vars
- Never add psutil as a hard import — always try/except it
- Never edit events.py without reading ALL 900+ lines first
  (it handles XP, AFK, counting, automod, AI personality, welcome, logging)
