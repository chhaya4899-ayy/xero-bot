#!/data/data/com.termux/files/usr/bin/bash
# XERO Bot — auto-start script
# This runs every time Termux is opened

BOT_DIR="$HOME/xero-bot"
SESSION_NAME="xero"

# Check if bot is already running
if screen -list | grep -q "$SESSION_NAME"; then
    echo "✅ XERO is already running."
    echo "   To see logs: screen -r $SESSION_NAME"
    echo "   To stop:     screen -S $SESSION_NAME -X quit"
else
    echo "🚀 Starting XERO Bot..."
    cd "$BOT_DIR"
    screen -dmS "$SESSION_NAME" python main.py
    sleep 2
    if screen -list | grep -q "$SESSION_NAME"; then
        echo "✅ XERO is running in the background."
        echo "   To see logs: screen -r $SESSION_NAME"
    else
        echo "❌ Something went wrong. Run: cd ~/xero-bot && python main.py"
    fi
fi
