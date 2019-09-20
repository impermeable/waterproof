FROM node:lts

RUN apt-get update && apt-get install -y \
    cloc \
    dc \
    jq \
    libasound2 \
#    libdbus-1-3 \
    libgconf-2-4 \
    libgtk-3-0 \
    libnss3 \
    libx11-xcb1 \
    libxss1 \
    libxtst6 \
    rsync \
    sudo \
    xvfb

RUN echo "node ALL=(ALL:ALL) NOPASSWD:ALL" > /etc/sudoers.d/node && \
    chmod 0440 /etc/sudoers.d/node

USER node
