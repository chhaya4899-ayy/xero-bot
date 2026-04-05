FROM python:3.11-slim

# Install system dependencies
# ffmpeg: required for audio processing
# libopus0: required for Discord voice (Opus codec)
# libsodium-dev, libnacl-dev, libffi-dev: required for PyNaCl (voice encryption)
RUN apt-get update && apt-get install -y \
    ffmpeg \
    libopus0 \
    libsodium-dev \
    libnacl-dev \
    libffi-dev \
    git \
    fonts-dejavu-core \
    fonts-liberation \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY requirements.txt .
# Ensure PyNaCl is installed to handle voice encryption
RUN pip install --no-cache-dir -r requirements.txt PyNaCl

COPY . .

RUN mkdir -p data/welcome_images logs

ENV PORT=8080

CMD ["python", "main.py"]
