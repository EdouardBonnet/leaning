const fs = require("node:fs");
const http = require("node:http");
const path = require("node:path");
const { spawn, spawnSync } = require("node:child_process");

const here = __dirname;
const sourceRoot = path.resolve(here, "../twin-width");
const dataFile = path.join(here, "lean-data.js");
const port = Number(process.env.PORT || 4173);
const host = process.env.HOST || "127.0.0.1";

const mimeTypes = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".svg": "image/svg+xml",
};

const server = http.createServer(async (request, response) => {
  try {
    const url = new URL(request.url, `http://${request.headers.host || "localhost"}`);
    if (url.pathname === "/api/status") {
      return sendJson(response, {
        ok: true,
        sourceRoot,
        compileAvailable: commandAvailable("lake"),
      });
    }
    if (url.pathname === "/api/import" && request.method === "POST") return importLeanFile(request, response);
    if (url.pathname === "/api/compile" && request.method === "POST") return compileNode(request, response);
    return serveStatic(url.pathname, response);
  } catch (error) {
    sendJson(response, { error: error.message }, 500);
  }
});

server.listen(port, host, () => {
  console.log(`Leaneage: http://${host}:${port}/`);
});

async function importLeanFile(request, response) {
  const body = await readJson(request);
  const relativePath = normalizeLeanPath(body.path);
  if (!relativePath) return sendJson(response, { error: "Path must be relative and end in .lean." }, 400);
  if (typeof body.content !== "string") return sendJson(response, { error: "Missing file content." }, 400);

  const destination = safeJoin(sourceRoot, relativePath);
  fs.mkdirSync(path.dirname(destination), { recursive: true });
  fs.writeFileSync(destination, body.content.replace(/\r\n/g, "\n"), "utf8");
  regenerateData();
  sendJson(response, { ok: true, path: relativePath, data: readData() });
}

async function compileNode(request, response) {
  const body = await readJson(request);
  const relativePath = normalizeNodePath(body.path || "");
  const type = body.type === "dir" ? "dir" : "file";
  const targets = compileTargets(relativePath, type);
  const args = ["build", ...targets];
  if (!commandAvailable("lake")) {
    return sendJson(response, {
      ok: false,
      command: `lake ${args.join(" ")}`,
      output:
        "Server-side Lean compilation is not available in this deployment because lake is not on PATH. " +
        "The current Render configuration is Node-only for faster deploys; install Lean/elan in the service environment if server-side Compile is required.",
    });
  }
  const output = await run("lake", args, sourceRoot);
  sendJson(response, {
    ok: output.code === 0,
    command: `lake ${args.join(" ")}`,
    output: trimOutput(output.text),
  });
}

function commandAvailable(command) {
  const result = spawnSync(command, ["--version"], { encoding: "utf8" });
  return result.status === 0;
}

function compileTargets(relativePath, type) {
  if (!relativePath) return [];
  const absolute = safeJoin(sourceRoot, relativePath);
  if (type === "file") {
    if (!absolute.endsWith(".lean") || !fs.existsSync(absolute)) {
      throw new Error("Selected Lean file does not exist.");
    }
    return [moduleName(relativePath)];
  }
  if (!fs.existsSync(absolute) || !fs.statSync(absolute).isDirectory()) {
    throw new Error("Selected folder does not exist.");
  }
  return walk(absolute)
    .filter((file) => file.endsWith(".lean"))
    .map((file) => moduleName(path.relative(sourceRoot, file).split(path.sep).join("/")));
}

function regenerateData() {
  const result = spawnSync(
    process.execPath,
    [path.join(here, "scripts/generate-data.mjs"), sourceRoot, dataFile],
    { cwd: here, encoding: "utf8" },
  );
  if (result.status !== 0) {
    throw new Error(result.stderr || result.stdout || "Data generation failed.");
  }
}

function readData() {
  const raw = fs.readFileSync(dataFile, "utf8");
  const match = raw.match(/^window\.LEAN_VIEWER_DATA = (.*);\n?$/s);
  if (!match) throw new Error("Could not parse lean-data.js.");
  return JSON.parse(match[1]);
}

function serveStatic(urlPath, response) {
  const requested = decodeURIComponent(urlPath === "/" ? "/index.html" : urlPath);
  const absolute = safeJoin(here, requested.replace(/^\/+/, ""));
  if (!fs.existsSync(absolute) || fs.statSync(absolute).isDirectory()) {
    response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
    response.end("Not found");
    return;
  }
  const ext = path.extname(absolute);
  response.writeHead(200, { "Content-Type": mimeTypes[ext] || "application/octet-stream" });
  fs.createReadStream(absolute).pipe(response);
}

function readJson(request) {
  return new Promise((resolve, reject) => {
    let body = "";
    request.setEncoding("utf8");
    request.on("data", (chunk) => {
      body += chunk;
      if (body.length > 8_000_000) {
        reject(new Error("Request body is too large."));
        request.destroy();
      }
    });
    request.on("end", () => {
      try {
        resolve(JSON.parse(body || "{}"));
      } catch (error) {
        reject(error);
      }
    });
    request.on("error", reject);
  });
}

function sendJson(response, payload, status = 200) {
  response.writeHead(status, { "Content-Type": "application/json; charset=utf-8" });
  response.end(JSON.stringify(payload));
}

function run(command, args, cwd) {
  return new Promise((resolve) => {
    const child = spawn(command, args, { cwd, shell: false });
    let text = "";
    child.stdout.on("data", (chunk) => {
      text += chunk.toString();
    });
    child.stderr.on("data", (chunk) => {
      text += chunk.toString();
    });
    child.on("error", (error) => {
      resolve({ code: 1, text: error.message });
    });
    child.on("close", (code) => {
      resolve({ code, text });
    });
  });
}

function trimOutput(text) {
  const limit = 40_000;
  if (text.length <= limit) return text;
  return `${text.slice(0, 4_000)}\n\n... output truncated ...\n\n${text.slice(-32_000)}`;
}

function normalizeLeanPath(input) {
  const normalized = normalizeNodePath(input);
  if (!normalized.endsWith(".lean")) return "";
  return normalized;
}

function normalizeNodePath(input) {
  const normalized = String(input || "").trim().replace(/\\/g, "/").replace(/^\/+/, "");
  if (!normalized) return "";
  if (normalized.split("/").some((part) => !part || part === "." || part === "..")) return "";
  return normalized;
}

function safeJoin(root, relativePath) {
  const absolute = path.resolve(root, relativePath);
  const relative = path.relative(root, absolute);
  if (relative.startsWith("..") || path.isAbsolute(relative)) {
    throw new Error("Path escapes the allowed root.");
  }
  return absolute;
}

function walk(root) {
  const entries = fs.readdirSync(root, { withFileTypes: true });
  const output = [];
  for (const entry of entries) {
    if (entry.name === ".lake" || entry.name === ".git") continue;
    const current = path.join(root, entry.name);
    if (entry.isDirectory()) output.push(...walk(current));
    else output.push(current);
  }
  return output;
}

function moduleName(filePath) {
  return filePath.replace(/\.lean$/, "").split("/").join(".");
}
