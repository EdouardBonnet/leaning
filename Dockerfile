FROM leanprover/lean4:v4.30.0-rc2

USER root
ENV PATH=/home/lean/.elan/bin:/root/.elan/bin:$PATH

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    ca-certificates \
    git \
    nodejs \
    zstd \
  && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY twin-width ./twin-width
COPY twin-width-viewer ./twin-width-viewer

WORKDIR /app/twin-width
RUN lake --version \
  && (lake exe cache get || true)

WORKDIR /app/twin-width-viewer
RUN node scripts/generate-data.mjs ../twin-width lean-data.js

ENV HOST=0.0.0.0
ENV NODE_ENV=production

EXPOSE 10000

CMD ["node", "server.js"]
