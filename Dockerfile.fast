FROM node:22-alpine

WORKDIR /app

COPY twin-width ./twin-width
COPY twin-width-viewer ./twin-width-viewer

WORKDIR /app/twin-width-viewer
RUN node scripts/generate-data.mjs ../twin-width lean-data.js

ENV HOST=0.0.0.0
ENV NODE_ENV=production

EXPOSE 10000

CMD ["node", "server.js"]
