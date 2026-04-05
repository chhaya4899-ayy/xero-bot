#!/data/data/com.termux/files/usr/bin/bash

echo ""
echo "==============================="
echo "   XERO Bot Setup"
echo "==============================="
echo ""
echo "Paste each key and press Enter"
echo ""

read -p "DISCORD_TOKEN: " DISCORD_TOKEN
read -p "MANAGEMENT_GUILD_ID: " MGUILD
read -p "NVIDIA_MAIN_KEY: " NVIDIA_MAIN
read -p "NVIDIA_VISION_KEY: " NVIDIA_VISION

# Write .env file
cat > .env << EOF
DISCORD_TOKEN=$DISCORD_TOKEN
MANAGEMENT_GUILD_ID=$MGUILD
NVIDIA_MAIN_KEY=$NVIDIA_MAIN
NVIDIA_VISION_KEY=$NVIDIA_VISION
NVIDIA_AUDIO_KEY=$NVIDIA_MAIN
EOF

echo ""
echo "✅ Keys saved!"
echo ""
echo "Starting bot..."
screen -dmS xero python main.py
sleep 2
echo "✅ Bot is running in the background!"
echo ""
echo "To check logs anytime type:  screen -r xero"
echo "To stop the bot type:        screen -S xero -X quit"
