FROM registry.hub.docker.com/pandoc/latex:3-ubuntu AS latex

FROM mcr.microsoft.com/devcontainers/typescript-node:18

RUN apt update \
    && export DEBIAN_FRONTEND=noninteractive \
    # For running integration tests in the terminal
    && apt install -y libgtk-3-dev xvfb \
    # For using tlaplus tools in the debug window
    && apt install -y openjdk-11-jre \
    && rm -rf /var/lib/apt/lists/*

# Add minimal latex instalation for tlaplus tools
COPY --from=latex /opt/texlive /opt/texlive
ENV PATH="${PATH}:/opt/texlive/texdir/bin/default"
