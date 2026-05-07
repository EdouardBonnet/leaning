FROM node:22-bookworm-slim

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    bash \
    ca-certificates \
    curl \
    git \
    unzip \
    xz-utils \
    zstd \
  && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/usr/local/elan
ENV PATH=/usr/local/elan/bin:$PATH

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none

WORKDIR /app

COPY twin-width ./twin-width
COPY twin-width-viewer ./twin-width-viewer

WORKDIR /app/twin-width
RUN elan toolchain install "$(cat lean-toolchain)" \
  && lake --version \
  && (lake exe cache get || true)

WORKDIR /app/twin-width-viewer
RUN node scripts/generate-data.mjs ../twin-width lean-data.js

ENV HOST=0.0.0.0
ENV NODE_ENV=production

EXPOSE 10000

CMD ["node", "server.js"]
