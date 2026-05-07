import fs from "node:fs";
import path from "node:path";

const sourceRoot = path.resolve(process.argv[2] || "../twin-width");
const outputFile = path.resolve(process.argv[3] || "lean-data.js");
const declarationPattern =
  /^\s*(?:(?:noncomputable|private|protected|partial|unsafe|scoped)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\b\s*([A-Za-z_][A-Za-z0-9_'.!?]*)?/;
const definitionKinds = new Set(["def", "abbrev", "structure", "class", "inductive", "opaque"]);

if (!fs.existsSync(sourceRoot)) {
  throw new Error(`Lean source root does not exist: ${sourceRoot}`);
}

const leanFiles = walk(sourceRoot)
  .filter((file) => file.endsWith(".lean"))
  .sort((a, b) => relativePath(a).localeCompare(relativePath(b)));

const files = leanFiles.map((absolutePath) => {
  const source = fs.readFileSync(absolutePath, "utf8").replace(/\r\n/g, "\n");
  const lines = source.endsWith("\n") ? source.slice(0, -1).split("\n") : source.split("\n");
  const filePath = relativePath(absolutePath);
  const declarations = collectDeclarations(filePath, lines);
  return {
    path: filePath,
    module: moduleName(filePath),
    isContract: filePath.endsWith("Contract.lean"),
    isDefs: filePath.endsWith("Defs.lean"),
    lines,
    declarations,
  };
});

const totalDeclarations = files.reduce((sum, file) => sum + file.declarations.length, 0);
const totalTargets = files.reduce(
  (sum, file) => sum + file.declarations.filter((decl) => decl.votable).length,
  0,
);

const payload = {
  version: 1,
  generatedAt: new Date().toISOString(),
  sourceRoot: path.relative(path.dirname(outputFile), sourceRoot).split(path.sep).join("/"),
  fileCount: files.length,
  declarationCount: totalDeclarations,
  targetCount: totalTargets,
  files,
};

fs.writeFileSync(
  outputFile,
  `window.LEAN_VIEWER_DATA = ${JSON.stringify(payload)};\n`,
  "utf8",
);

console.log(
  `Generated ${path.relative(process.cwd(), outputFile)} from ${files.length} Lean files with ${totalTargets} votable statements.`,
);

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

function relativePath(file) {
  return path.relative(sourceRoot, file).split(path.sep).join("/");
}

function moduleName(filePath) {
  return filePath.replace(/\.lean$/, "").split("/").join(".");
}

function collectDeclarations(filePath, lines) {
  const declarations = [];
  const namespaces = [];
  const isContract = filePath.endsWith("Contract.lean");
  const isDefs = filePath.endsWith("Defs.lean");

  lines.forEach((line, index) => {
    const namespaceMatch = line.match(/^namespace\s+(.+?)\s*$/);
    if (namespaceMatch) {
      namespaces.push(...namespaceMatch[1].split(/\s+/).filter(Boolean));
      return;
    }

    if (/^end(?:\s+[A-Za-z0-9_'.]+)?\s*$/.test(line)) {
      namespaces.pop();
      return;
    }

    const declarationMatch = line.match(declarationPattern);
    if (!declarationMatch) return;

    const kind = declarationMatch[1];
    const rawName = declarationMatch[2];
    const generatedName = `${kind}_at_line_${index + 1}`;
    const name = rawName && !rawName.startsWith(":") ? rawName : generatedName;
    const namespace = namespaces.join(".");
    const fullName = namespace ? `${namespace}.${name}` : name;
    const tags = [];
    if (isContract) tags.push("contract");
    if (isDefs) tags.push("defs");
    if (definitionKinds.has(kind)) tags.push("definition");

    declarations.push({
      id: `${filePath}#${fullName}:${index + 1}`,
      kind,
      name,
      fullName,
      namespace,
      line: index + 1,
      endLine: index + 1,
      signature: extractSignature(lines, index),
      doc: extractDoc(lines, index),
      tags,
      votable: isContract || isDefs || definitionKinds.has(kind),
    });
  });

  declarations.forEach((decl, index) => {
    const next = declarations[index + 1];
    decl.endLine = next ? next.line - 1 : lines.length;
  });

  return declarations;
}

function extractSignature(lines, startIndex) {
  const collected = [];
  for (let index = startIndex; index < Math.min(lines.length, startIndex + 16); index += 1) {
    const line = lines[index];
    collected.push(line);
    const trimmed = line.trim();
    if (
      trimmed.includes(" := ") ||
      trimmed.endsWith(" := by") ||
      trimmed.endsWith(" := by") ||
      trimmed.endsWith(" where") ||
      trimmed === "where"
    ) {
      break;
    }
  }
  return collected.join("\n");
}

function extractDoc(lines, declarationIndex) {
  let index = declarationIndex - 1;
  while (index >= 0) {
    const trimmed = lines[index].trim();
    if (!trimmed || trimmed.startsWith("@[")) {
      index -= 1;
      continue;
    }
    break;
  }

  if (index < 0 || !lines[index].includes("-/")) return "";

  const end = index;
  let start = end;
  while (start >= 0 && !lines[start].includes("/--")) start -= 1;
  if (start < 0) return "";

  return cleanDoc(lines.slice(start, end + 1).join("\n"));
}

function cleanDoc(raw) {
  return raw
    .replace(/^\s*\/--\s?/, "")
    .replace(/\s*-\/\s*$/, "")
    .split("\n")
    .map((line) => line.replace(/^\s*\*?\s?/, "").trimEnd())
    .join("\n")
    .trim();
}
