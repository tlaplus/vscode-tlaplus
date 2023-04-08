FROM mcr.microsoft.com/devcontainers/typescript-node:18

RUN apt update \
    && export DEBIAN_FRONTEND=noninteractive \
    && apt install -y libasound2 libgbm-dev libgtk-3-0 libatk-bridge2.0-0 libnss3 libxshmfence1 xvfb \
    && rm -rf /var/lib/apt/lists/*

# Set default container user group as root to be able to edit files in vscode
RUN usermod --gid root node
