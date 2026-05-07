(function () {
  "use strict";

  let data = window.LEAN_VIEWER_DATA;
  if (!data || !Array.isArray(data.files)) {
    throw new Error("Missing Lean viewer data. Run scripts/generate-data.mjs first.");
  }

  let files = [];
  let fileByPath = new Map();
  let allDeclarations = [];
  let votableDeclarations = [];
  let declarationById = new Map();
  let tree = null;
  let dirPaths = new Set();

  const els = {
    search: document.getElementById("globalSearch"),
    fileTree: document.getElementById("fileTree"),
    fileCount: document.getElementById("fileCount"),
    breadcrumb: document.getElementById("breadcrumb"),
    fileTitle: document.getElementById("fileTitle"),
    fileStats: document.getElementById("fileStats"),
    codeView: document.getElementById("codeView"),
    selectionToolbar: document.getElementById("selectionToolbar"),
    selectionIssueButton: document.getElementById("selectionIssueButton"),
    raisedItems: document.getElementById("raisedItems"),
    candidateItems: document.getElementById("candidateItems"),
    raisedCount: document.getElementById("raisedCount"),
    candidateCount: document.getElementById("candidateCount"),
    accountButton: document.getElementById("accountButton"),
    accountModal: document.getElementById("accountModal"),
    accountForm: document.getElementById("accountForm"),
    accountName: document.getElementById("accountName"),
    accountPassword: document.getElementById("accountPassword"),
    accountError: document.getElementById("accountError"),
    accountLogout: document.getElementById("accountLogout"),
    accountCancel: document.getElementById("accountCancel"),
    themeToggle: document.getElementById("themeToggle"),
    sourceImportButton: document.getElementById("sourceImportButton"),
    sourceImportFile: document.getElementById("sourceImportFile"),
    compileButton: document.getElementById("compileButton"),
    compileOutputPanel: document.getElementById("compileOutputPanel"),
    clearOutputButton: document.getElementById("clearOutputButton"),
    toolOutput: document.getElementById("toolOutput"),
    issueModal: document.getElementById("issueModal"),
    issueForm: document.getElementById("issueForm"),
    issueExcerpt: document.getElementById("issueExcerpt"),
    issueComment: document.getElementById("issueComment"),
    issueCancel: document.getElementById("issueCancel"),
  };

  const appState = {
    file: null,
    selectedNode: null,
    selectedLine: null,
    query: "",
    serverAvailable: false,
    compileAvailable: false,
    selectedIssue: null,
  };

  const storeKey = "twinWidthConformState.v2";
  const oldVoteKey = "twinWidthFormalizationVotes.v1";
  let store = readStore();
  const moderatorUsernames = new Set(["edouardbonnet", "ebonnet"]);

  const declarationPattern =
    /^\s*(?:(?:noncomputable|private|protected|partial|unsafe|scoped)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\b\s*([A-Za-z_][A-Za-z0-9_'.!?]*)?/;
  const definitionKinds = new Set(["def", "abbrev", "structure", "class", "inductive", "opaque"]);
  const declarationKeywords = new Set([
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "class",
    "inductive",
    "instance",
    "axiom",
    "opaque",
  ]);
  const leanKeywords = new Set(
    [
      "abbrev",
      "axiom",
      "by",
      "calc",
      "case",
      "class",
      "def",
      "deriving",
      "do",
      "else",
      "end",
      "example",
      "exists",
      "forall",
      "fun",
      "have",
      "if",
      "import",
      "in",
      "inductive",
      "instance",
      "let",
      "lemma",
      "match",
      "namespace",
      "noncomputable",
      "opaque",
      "open",
      "private",
      "protected",
      "return",
      "section",
      "simp",
      "structure",
      "syntax",
      "theorem",
      "then",
      "universe",
      "variable",
      "where",
      "with",
    ].join(" ").split(" "),
  );

  init();

  function init() {
    setData(data);
    applyTheme();
    updateAccountUI();

    els.search.addEventListener("input", () => {
      appState.query = els.search.value.trim().toLowerCase();
      renderNavigation();
      renderInspector();
    });

    setupDiscreteScrollbars();

    els.accountButton.addEventListener("click", openAccountModal);
    els.accountCancel.addEventListener("click", closeAccountModal);
    els.accountLogout.addEventListener("click", logout);
    els.accountModal.addEventListener("click", (event) => {
      if (event.target === els.accountModal) closeAccountModal();
    });
    els.accountForm.addEventListener("submit", saveAccount);
    els.themeToggle.addEventListener("click", toggleTheme);
    els.sourceImportButton.addEventListener("click", () => els.sourceImportFile.click());
    els.sourceImportFile.addEventListener("change", importLeanFile);
    els.compileButton.addEventListener("click", compileSelectedNode);
    els.clearOutputButton.addEventListener("click", () => {
      els.compileOutputPanel.hidden = true;
      els.toolOutput.textContent = "";
    });
    els.selectionIssueButton.addEventListener("click", openSelectionIssueModal);
    els.issueCancel.addEventListener("click", closeIssueModal);
    els.issueModal.addEventListener("click", (event) => {
      if (event.target === els.issueModal) closeIssueModal();
    });
    els.issueForm.addEventListener("submit", saveSelectedIssue);

    els.codeView.addEventListener("click", (event) => {
      const lineButton = event.target.closest("[data-line]");
      if (lineButton && appState.file) {
        navigateTo(appState.file.path, Number(lineButton.dataset.line));
      }
    });
    els.codeView.addEventListener("mouseup", () => {
      window.setTimeout(handleSourceSelection, 0);
    });
    els.codeView.addEventListener("keyup", handleSourceSelection);

    document.body.addEventListener("click", (event) => {
      const conform = event.target.closest("[data-conform-id]");
      if (conform) {
        setConform(conform.dataset.conformId, Number(conform.dataset.conformValue));
        return;
      }

      const reply = event.target.closest("[data-report-reply]");
      if (reply) {
        replyToReport(reply.dataset.reportDecl, reply.dataset.reportReply);
        return;
      }

      const remove = event.target.closest("[data-report-remove]");
      if (remove) {
        removeReport(remove.dataset.reportDecl, remove.dataset.reportRemove);
        return;
      }

      const jump = event.target.closest("[data-decl-id]");
      if (jump) {
        const decl = declarationById.get(jump.dataset.declId);
        if (decl) navigateTo(decl.filePath, decl.line);
      }

      const nodeButton = event.target.closest("[data-node-path]");
      if (nodeButton) {
        selectNode(nodeButton.dataset.nodePath, nodeButton.dataset.nodeType);
      }
    });

    window.addEventListener("hashchange", () => openFromHash());
    checkServer();
    openFromHash();
    renderAll();
  }

  function setupDiscreteScrollbars() {
    const scrollables = [els.fileTree, els.codeView, document.querySelector(".sidebar"), document.querySelector(".inspector")].filter(Boolean);
    for (const element of scrollables) {
      let timeout = 0;
      element.addEventListener(
        "scroll",
        () => {
          element.classList.add("is-scrolling");
          window.clearTimeout(timeout);
          timeout = window.setTimeout(() => element.classList.remove("is-scrolling"), 800);
        },
        { passive: true },
      );
    }
  }

  function setData(nextData) {
    data = nextData;
    files = [...data.files].sort((a, b) => a.path.localeCompare(b.path));
    fileByPath = new Map(files.map((file) => [file.path, file]));
    allDeclarations = files
      .flatMap((file) =>
        file.declarations.map((decl) => ({
          ...decl,
          filePath: file.path,
          file,
        })),
      )
      .sort((a, b) => a.filePath.localeCompare(b.filePath) || a.line - b.line);
    votableDeclarations = allDeclarations.filter((decl) => decl.votable);
    declarationById = new Map(votableDeclarations.map((decl) => [decl.id, decl]));
    tree = buildTree(files);
    dirPaths = collectDirPaths(files);
  }

  function renderAll() {
    els.fileCount.textContent = `${files.length} Lean files`;
    renderNavigation();
    if (appState.selectedNode?.type === "dir") {
      renderFolderView(appState.selectedNode.path);
    } else if (appState.file) {
      renderFileHeader();
      renderCode();
    }
    renderInspector();
    refreshStatus();
  }

  function buildTree(inputFiles) {
    const root = { type: "dir", name: "", path: "", children: new Map() };
    for (const file of inputFiles) {
      const parts = file.path.split("/");
      let node = root;
      parts.forEach((part, index) => {
        const isFile = index === parts.length - 1;
        const childPath = parts.slice(0, index + 1).join("/");
        if (!node.children.has(part)) {
          node.children.set(part, {
            type: isFile ? "file" : "dir",
            name: part,
            path: childPath,
            children: new Map(),
            file: isFile ? file : null,
          });
        }
        node = node.children.get(part);
        if (isFile) node.file = file;
      });
    }
    return root;
  }

  function collectDirPaths(inputFiles) {
    const paths = new Set([""]);
    for (const file of inputFiles) {
      const parts = file.path.split("/");
      for (let index = 1; index < parts.length; index += 1) {
        paths.add(parts.slice(0, index).join("/"));
      }
    }
    return paths;
  }

  function sortedChildren(node) {
    return Array.from(node.children.values()).sort((a, b) => {
      if (a.type !== b.type) return a.type === "dir" ? -1 : 1;
      return a.name.localeCompare(b.name);
    });
  }

  function renderNavigation() {
    els.fileTree.replaceChildren();
    const fragment = document.createDocumentFragment();
    for (const child of sortedChildren(tree)) renderTreeNode(child, fragment, 0);
    els.fileTree.appendChild(fragment);
  }

  function renderTreeNode(node, parent, depth) {
    if (!nodeMatchesSearch(node)) return;

    if (node.type === "dir") {
      const details = document.createElement("details");
      details.className = "tree-folder";
      details.open = depth < 2 || Boolean(appState.query) || selectedInside(node.path);
      details.classList.toggle(
        "is-active",
        appState.selectedNode?.type === "dir" && appState.selectedNode.path === node.path,
      );

      const summary = document.createElement("summary");
      summary.dataset.nodePath = node.path;
      summary.dataset.nodeType = "dir";
      summary.appendChild(textSpan("folder-name", node.name));
      summary.appendChild(makeTreeBadge(node.path, "dir"));
      details.appendChild(summary);

      const children = document.createElement("div");
      children.className = "tree-children";
      for (const child of sortedChildren(node)) renderTreeNode(child, children, depth + 1);
      details.appendChild(children);
      parent.appendChild(details);
      return;
    }

    const file = node.file;
    const button = document.createElement("button");
    button.type = "button";
    button.className = "file-node";
    button.classList.toggle(
      "is-active",
      appState.selectedNode?.type === "file" && appState.selectedNode.path === file.path,
    );
    button.dataset.nodePath = file.path;
    button.dataset.nodeType = "file";

    const name = document.createElement("span");
    name.className = "file-name";
    name.textContent = node.name;
    button.appendChild(name);
    button.appendChild(makeTreeBadge(file.path, "file"));
    parent.appendChild(button);
  }

  function selectedInside(path) {
    const selectedPath = appState.selectedNode?.path || appState.file?.path || "";
    return selectedPath === path || selectedPath.startsWith(`${path}/`);
  }

  function makeTreeBadge(path, type) {
    const stats = validationStatsForNode(path, type);
    const badge = document.createElement("span");
    badge.className = "file-badge";
    badge.textContent = stats.total ? `${stats.validated}/${stats.total}` : "";
    badge.title = stats.total ? `${stats.validated} validated among ${stats.total}` : "";
    return badge;
  }

  function nodeMatchesSearch(node) {
    if (!appState.query) return true;
    if (node.type === "file") return fileMatchesSearch(node.file);
    return sortedChildren(node).some((child) => nodeMatchesSearch(child));
  }

  function fileMatchesSearch(file) {
    const query = appState.query;
    return (
      file.path.toLowerCase().includes(query) ||
      file.module.toLowerCase().includes(query) ||
      file.declarations.some((decl) => declarationSearchText(decl, file).includes(query))
    );
  }

  function openFromHash() {
    const target = parseHash();
    if (target && fileByPath.has(target.path)) {
      selectNode(target.path, "file", target.line, true);
      return;
    }
    if (target && dirPaths.has(target.path)) {
      selectNode(target.path, "dir", null, true);
      return;
    }
    const firstFile = files.find((file) => file.path === "TwinWidth.lean") || files[0];
    selectNode(firstFile.path, "file", null, true);
  }

  function parseHash() {
    const raw = window.location.hash.slice(1);
    if (!raw) return null;
    const decoded = decodeURIComponent(raw);
    const colon = decoded.lastIndexOf(":");
    if (colon !== -1) {
      const maybeLine = decoded.slice(colon + 1);
      if (/^\d+$/.test(maybeLine)) return { path: decoded.slice(0, colon), line: Number(maybeLine) };
    }
    return { path: decoded, line: null };
  }

  function navigateTo(path, line = null) {
    const hash = `#${encodeURIComponent(path)}${line ? `:${line}` : ""}`;
    if (window.location.hash === hash) {
      selectNode(path, fileByPath.has(path) ? "file" : "dir", line, true);
    } else {
      window.location.hash = hash;
    }
  }

  function selectNode(path, type, line = null, fromHash = false) {
    if (type === "file" && !fileByPath.has(path)) return;
    if (type === "dir" && !dirPaths.has(path)) return;

    appState.selectedNode = { path, type };
    appState.selectedLine = line;
    appState.file = type === "file" ? fileByPath.get(path) : null;

    if (!fromHash) navigateTo(path, line);
    renderAll();

    if (type === "file" && line) {
      requestAnimationFrame(() => {
        document.getElementById(`L${line}`)?.scrollIntoView({ block: "center" });
      });
    }
  }

  function renderFileHeader() {
    const file = appState.file;
    const parts = file.path.split("/");
    els.breadcrumb.textContent = parts.slice(0, -1).join(" / ");
    els.fileTitle.textContent = parts.at(-1);

    const stats = validationStatsForNode(file.path, "file");
    const raised = declarationsForNode(file.path, "file").filter((decl) => hasReports(decl.id)).length;
    const tags = [];
    if (file.isContract) tags.push("contract");
    if (file.isDefs) tags.push("defs");

    els.fileStats.replaceChildren(
      statBadge(`${file.lines.length} lines`),
      statBadge(`${stats.validated}/${stats.total} validated`),
      statBadge(`${raised} raised`),
      ...tags.map((tag) => {
        const span = document.createElement("span");
        span.className = `tag ${tag === "contract" ? "contract" : "definition"}`;
        span.textContent = tag;
        return span;
      }),
    );
  }

  function renderFolderView(path) {
    const name = path || "Lean root";
    const stats = validationStatsForNode(path, "dir");
    const raised = declarationsForNode(path, "dir").filter((decl) => hasReports(decl.id)).length;
    els.breadcrumb.textContent = "Folder";
    els.fileTitle.textContent = name;
    els.fileStats.replaceChildren(
      statBadge(`${stats.validated}/${stats.total} validated`),
      statBadge(`${raised} raised`),
    );

    const container = document.createElement("div");
    container.className = "folder-view";
    container.appendChild(textBlock("h3", "Selected Node"));
    container.appendChild(
      textBlock(
        "p",
        "Use Import .lean to add a file under this folder, or Compile to run lake build for this node when the local server is active.",
      ),
    );

    const list = document.createElement("div");
    list.className = "folder-grid";
    const node = findTreeNode(path);
    for (const child of node ? sortedChildren(node) : []) {
      const button = document.createElement("button");
      button.type = "button";
      button.dataset.nodePath = child.path;
      button.dataset.nodeType = child.type;
      button.className = "folder-card";
      button.appendChild(textSpan("folder-card-name", child.name));
      button.appendChild(makeTreeBadge(child.path, child.type));
      list.appendChild(button);
    }
    container.appendChild(list);
    els.codeView.replaceChildren(container);
  }

  function findTreeNode(path) {
    if (!path) return tree;
    return path.split("/").reduce((node, part) => node?.children.get(part), tree);
  }

  function renderCode() {
    const file = appState.file;
    hideSelectionToolbar();
    const declarationsByLine = new Map(
      file.declarations
        .filter((decl) => decl.votable)
        .map((decl) => [decl.line, { ...decl, filePath: file.path, file }]),
    );
    const highlighted = highlightLeanLines(file.lines);
    const container = document.createElement("div");
    container.className = "code-lines";

    file.lines.forEach((line, index) => {
      const lineNumber = index + 1;
      const declaration = declarationsByLine.get(lineNumber);
      const row = document.createElement("div");
      row.className = "code-line";
      row.id = `L${lineNumber}`;
      row.classList.toggle("is-target", Boolean(declaration));
      row.classList.toggle("is-selected", lineNumber === appState.selectedLine);
      row.classList.toggle("is-validated", declaration && isValidated(declaration.id));
      row.classList.toggle("is-raised", declaration && hasReports(declaration.id));

      const number = document.createElement("button");
      number.type = "button";
      number.className = "line-number";
      number.dataset.line = String(lineNumber);
      number.textContent = String(lineNumber);
      row.appendChild(number);

      const voteSlot = document.createElement("div");
      voteSlot.className = "line-vote";
      if (declaration) voteSlot.appendChild(makeConformTicks(declaration, "line"));
      row.appendChild(voteSlot);

      const code = document.createElement("code");
      code.className = "line-code";
      code.innerHTML = highlighted[index] || " ";
      row.appendChild(code);
      container.appendChild(row);
    });

    els.codeView.replaceChildren(container);
  }

  function handleSourceSelection() {
    if (!appState.file) {
      hideSelectionToolbar();
      return;
    }

    const selection = window.getSelection();
    if (!selection || selection.rangeCount === 0 || selection.isCollapsed) {
      hideSelectionToolbar();
      return;
    }

    const excerpt = selection.toString().trim();
    if (!excerpt) {
      hideSelectionToolbar();
      return;
    }

    const range = selection.getRangeAt(0);
    if (!els.codeView.contains(range.commonAncestorContainer)) {
      hideSelectionToolbar();
      return;
    }

    const anchorLine = closestLineNumber(selection.anchorNode);
    const focusLine = closestLineNumber(selection.focusNode);
    if (!anchorLine || !focusLine) {
      hideSelectionToolbar();
      return;
    }

    const startLine = Math.min(anchorLine, focusLine);
    const endLine = Math.max(anchorLine, focusLine);
    const declaration = declarationForLineRange(startLine, endLine);
    if (!declaration) {
      hideSelectionToolbar();
      return;
    }

    appState.selectedIssue = {
      declarationId: declaration.id,
      excerpt,
      startLine,
      endLine,
    };
    showSelectionToolbar(range);
  }

  function closestLineNumber(node) {
    const element = node.nodeType === Node.ELEMENT_NODE ? node : node.parentElement;
    const line = element?.closest(".code-line");
    if (!line?.id?.startsWith("L")) return 0;
    return Number(line.id.slice(1));
  }

  function declarationForLineRange(startLine, endLine) {
    const declaration = appState.file.declarations.find(
      (decl) => decl.votable && startLine >= decl.line && endLine <= decl.endLine,
    );
    if (!declaration) return null;
    return { ...declaration, filePath: appState.file.path, file: appState.file };
  }

  function showSelectionToolbar(range) {
    const rect = range.getBoundingClientRect();
    els.selectionIssueButton.disabled = !store.currentUser;
    els.selectionIssueButton.title = store.currentUser
      ? "Raise an issue for the selected excerpt"
      : "Login to raise an issue";
    els.selectionToolbar.hidden = false;
    const toolbarRect = els.selectionToolbar.getBoundingClientRect();
    const left = Math.min(
      Math.max(rect.left + rect.width / 2 - toolbarRect.width / 2, 12),
      window.innerWidth - toolbarRect.width - 12,
    );
    const top = Math.max(rect.top - toolbarRect.height - 10, 12);
    els.selectionToolbar.style.left = `${left}px`;
    els.selectionToolbar.style.top = `${top}px`;
  }

  function hideSelectionToolbar() {
    appState.selectedIssue = null;
    els.selectionToolbar.hidden = true;
  }

  function renderInspector() {
    const raised = votableDeclarations
      .filter((decl) => hasReports(decl.id))
      .filter(declarationMatchesSearch)
      .sort((a, b) => latestReportTime(b.id) - latestReportTime(a.id));
    const candidates = votableDeclarations
      .filter((decl) => !hasReports(decl.id) && !isValidated(decl.id))
      .filter(declarationMatchesSearch)
      .sort((a, b) => tally(b.id) - tally(a.id) || a.filePath.localeCompare(b.filePath));

    els.raisedCount.textContent = String(raised.length);
    els.candidateCount.textContent = String(candidates.length);

    renderDeclarationList(els.raisedItems, raised, "No raised items match the current search.", {
      compact: true,
      showReports: true,
    });
    renderDeclarationList(
      els.candidateItems,
      candidates,
      "No open items match the current search.",
      { compact: true },
    );
  }

  function renderDeclarationList(container, declarations, emptyText, options = {}) {
    container.replaceChildren();
    if (!declarations.length) {
      const empty = document.createElement("div");
      empty.className = "empty-state";
      empty.textContent = emptyText;
      container.appendChild(empty);
      return;
    }

    const fragment = document.createDocumentFragment();
    for (const decl of declarations) {
      const item = document.createElement("article");
      item.className = "decl-item";
      item.classList.toggle("is-validated", isValidated(decl.id));
      item.classList.toggle("is-raised", hasReports(decl.id));

      const jump = document.createElement("button");
      jump.type = "button";
      jump.className = "decl-jump";
      jump.dataset.declId = decl.id;

      const meta = document.createElement("span");
      meta.className = "decl-meta";
      const kind = document.createElement("span");
      kind.className = "decl-kind";
      kind.textContent = decl.kind;
      meta.appendChild(kind);
      if (!options.compact) meta.appendChild(statusChip(decl));
      jump.appendChild(meta);

      const name = document.createElement("span");
      name.className = "decl-name";
      name.innerHTML = highlightMatch(decl.fullName || decl.name);
      jump.appendChild(name);

      const location = document.createElement("span");
      location.className = "decl-location";
      location.innerHTML = highlightMatch(options.compact ? `${decl.filePath}:${decl.line}` : `${decl.filePath}:${decl.line}`);
      jump.appendChild(location);

      if (decl.doc && !options.compact) {
        const doc = document.createElement("span");
        doc.className = "decl-doc";
        doc.innerHTML = highlightMatch(trimDoc(decl.doc));
        jump.appendChild(doc);
      }

      item.appendChild(jump);
      item.appendChild(makeDeclarationActions(decl, { readOnly: true }));

      const reports = reportsFor(decl.id);
      if (reports.length && options.showReports) item.appendChild(makeReportList(reports, options.compact));
      fragment.appendChild(item);
    }
    container.appendChild(fragment);
  }

  function statusChip(decl) {
    const state = itemState(decl.id);
    const span = document.createElement("span");
    span.className = "status-chip";
    if (state.validated) {
      span.classList.add("validated");
      span.textContent = "Validated";
    } else {
      span.textContent = `${state.tally}/5 conform`;
    }
    if (state.reports.length) span.classList.add("raised");
    return span;
  }

  function makeDeclarationActions(decl, options = {}) {
    const actions = document.createElement("div");
    actions.className = "decl-actions";

    actions.appendChild(makeConformTicks(decl, "panel", options.readOnly));
    return actions;
  }

  function makeConformTicks(decl, variant, readOnly = false) {
    const state = itemState(decl.id);
    const group = document.createElement("div");
    group.className = `tick-group ${variant}`;
    group.title = readOnly
      ? `${state.tally}/5 conformity tally`
      : state.validated
      ? "Validated"
      : store.currentUser
        ? `${state.tally}/5 conformity tally`
        : "Login to conform";

    for (let index = 1; index <= 5; index += 1) {
      const tick = document.createElement("button");
      tick.type = "button";
      tick.className = "conform-tick";
      tick.textContent = "✓";
      tick.classList.toggle("filled", index <= Math.min(state.tally, 5));
      tick.classList.toggle("validated", state.validated);

      const value = conformValueForTick(state, index);
      if (!readOnly && value && store.currentUser && !state.validated) {
        tick.dataset.conformId = decl.id;
        tick.dataset.conformValue = String(value);
        tick.title = value === 2 ? "Conform: completely sure" : "Conform: checked";
      } else {
        tick.disabled = true;
        tick.title = state.validated
          ? "Validated"
          : store.currentUser
            ? `${state.tally}/5`
            : "Login to conform";
      }

      group.appendChild(tick);
    }
    return group;
  }

  function conformValueForTick(state, index) {
    if (state.validated || state.userVote === 2) return 0;
    if (state.userVote === 0) {
      if (index === state.tally + 1) return 1;
      if (index === state.tally + 2) return 2;
      return 0;
    }
    if (state.userVote === 1 && index === state.tally + 1) return 2;
    return 0;
  }

  function makeReportList(reports, compact) {
    const list = document.createElement("div");
    list.className = "report-list";
    const visibleReports = reports.slice(0, compact ? 2 : reports.length);
    for (const report of visibleReports) {
      const item = document.createElement("div");
      item.className = "report-item";
      if (report.excerpt) {
        const excerpt = document.createElement("pre");
        excerpt.className = "report-excerpt";
        const lineLabel =
          report.startLine && report.endLine && report.startLine !== report.endLine
            ? `L${report.startLine}-L${report.endLine}`
            : report.startLine
              ? `L${report.startLine}`
              : "";
        excerpt.textContent = lineLabel ? `${lineLabel} ${report.excerpt}` : report.excerpt;
        item.appendChild(excerpt);
      }
      const line = document.createElement("p");
      const author = report.user || "unknown";
      line.textContent = report.comment ? `${author}: ${report.comment}` : `${author}: raised as erroneous`;
      item.appendChild(line);

      if (report.replies?.length) {
        const replies = document.createElement("div");
        replies.className = "report-replies";
        for (const reply of report.replies.slice(0, compact ? 1 : report.replies.length)) {
          const replyLine = document.createElement("p");
          replyLine.textContent = `${reply.user || "unknown"}: ${reply.comment}`;
          replies.appendChild(replyLine);
        }
        item.appendChild(replies);
      }

      const actions = document.createElement("div");
      actions.className = "report-actions";
      const reply = actionButton("Reply", "text-button");
      reply.dataset.reportDecl = report.declarationId;
      reply.dataset.reportReply = report.id;
      reply.disabled = !store.currentUser;
      actions.appendChild(reply);

      if (canRemoveReport(report)) {
        const remove = actionButton("Remove", "text-button danger");
        remove.dataset.reportDecl = report.declarationId;
        remove.dataset.reportRemove = report.id;
        actions.appendChild(remove);
      }
      item.appendChild(actions);
      list.appendChild(item);
    }
    if (reports.length > visibleReports.length) {
      const more = document.createElement("p");
      more.className = "report-more";
      more.textContent = `${reports.length - visibleReports.length} more`;
      list.appendChild(more);
    }
    return list;
  }

  function declarationsForSelectedNode() {
    if (!appState.selectedNode) return [];
    return declarationsForNode(appState.selectedNode.path, appState.selectedNode.type);
  }

  function declarationsForNode(path, type) {
    if (type === "file") {
      const file = fileByPath.get(path);
      if (!file) return [];
      return file.declarations
        .filter((decl) => decl.votable)
        .map((decl) => ({ ...decl, filePath: file.path, file }));
    }
    const prefix = path ? `${path}/` : "";
    return votableDeclarations.filter((decl) => decl.filePath.startsWith(prefix));
  }

  function validationStatsForNode(path, type) {
    const declarations = declarationsForNode(path, type);
    return {
      total: declarations.length,
      validated: declarations.filter((decl) => isValidated(decl.id)).length,
    };
  }

  function declarationMatchesSearch(decl) {
    if (!appState.query) return true;
    return declarationSearchText(decl, decl.file).includes(appState.query);
  }

  function declarationSearchText(decl, file) {
    return [
      decl.kind,
      decl.name,
      decl.fullName,
      decl.doc,
      decl.signature,
      file ? file.path : decl.filePath,
      file ? file.module : "",
      ...(decl.tags || []),
    ]
      .join(" ")
      .toLowerCase();
  }

  function itemState(id) {
    const votes = store.conforms[id]?.votes || {};
    const userVote = store.currentUser ? Number(votes[store.currentUser] || 0) : 0;
    const score = Object.values(votes).reduce((sum, value) => sum + Number(value || 0), 0);
    return {
      tally: score,
      userVote,
      validated: score >= 5,
      reports: reportsFor(id),
    };
  }

  function tally(id) {
    return itemState(id).tally;
  }

  function isValidated(id) {
    return tally(id) >= 5;
  }

  function reportsFor(id) {
    return Array.isArray(store.reports[id]) ? store.reports[id] : [];
  }

  function hasReports(id) {
    return reportsFor(id).length > 0;
  }

  function latestReportTime(id) {
    return Math.max(0, ...reportsFor(id).map((report) => Date.parse(report.createdAt) || 0));
  }

  function setConform(id, value) {
    if (!declarationById.has(id) || isValidated(id)) return;
    const user = store.currentUser;
    if (!user) {
      showToolOutput("Login required", "Guests are read-only. Register or login to conform.");
      return;
    }
    const normalized = value === 2 ? 2 : 1;
    store.conforms[id] = store.conforms[id] || { votes: {} };
    store.conforms[id].votes[user] = normalized;
    store.conforms[id].updatedAt = new Date().toISOString();
    saveStore();
    renderAll();
  }

  function openSelectionIssueModal() {
    const selectionIssue = appState.selectedIssue;
    if (!selectionIssue || !declarationById.has(selectionIssue.declarationId)) return;
    const user = store.currentUser;
    if (!user) {
      showToolOutput("Login required", "Guests are read-only. Register or login to raise an issue.");
      return;
    }
    els.issueExcerpt.textContent = formatExcerpt(selectionIssue);
    els.issueComment.value = "";
    els.issueModal.hidden = false;
    requestAnimationFrame(() => els.issueComment.focus());
  }

  function closeIssueModal() {
    els.issueModal.hidden = true;
  }

  function saveSelectedIssue(event) {
    event.preventDefault();
    const selectionIssue = appState.selectedIssue;
    if (!selectionIssue || !declarationById.has(selectionIssue.declarationId)) {
      closeIssueModal();
      return;
    }
    const user = store.currentUser;
    if (!user) {
      closeIssueModal();
      showToolOutput("Login required", "Guests are read-only. Register or login to raise an issue.");
      return;
    }
    const comment = els.issueComment.value.trim();
    if (!comment) {
      els.issueComment.focus();
      return;
    }
    const id = selectionIssue.declarationId;
    store.reports[id] = reportsFor(id);
    store.reports[id].push({
      id: makeId(),
      declarationId: id,
      user,
      comment,
      excerpt: selectionIssue.excerpt,
      startLine: selectionIssue.startLine,
      endLine: selectionIssue.endLine,
      createdAt: new Date().toISOString(),
      replies: [],
    });
    saveStore();
    closeIssueModal();
    hideSelectionToolbar();
    window.getSelection()?.removeAllRanges();
    renderAll();
  }

  function formatExcerpt(selectionIssue) {
    const lines =
      selectionIssue.startLine === selectionIssue.endLine
        ? `L${selectionIssue.startLine}`
        : `L${selectionIssue.startLine}-L${selectionIssue.endLine}`;
    return `${lines}\n${selectionIssue.excerpt}`;
  }

  function replyToReport(declarationId, reportId) {
    if (!store.currentUser) {
      showToolOutput("Login required", "Guests are read-only. Register or login to answer an issue.");
      return;
    }
    const reports = reportsFor(declarationId);
    const report = reports.find((item) => item.id === reportId);
    if (!report) return;
    const comment = window.prompt("Reply to this issue:", "") || "";
    if (!comment.trim()) return;
    report.replies = Array.isArray(report.replies) ? report.replies : [];
    report.replies.push({
      id: makeId(),
      user: store.currentUser,
      comment: comment.trim(),
      createdAt: new Date().toISOString(),
    });
    store.reports[declarationId] = reports;
    saveStore();
    renderAll();
  }

  function removeReport(declarationId, reportId) {
    const reports = reportsFor(declarationId);
    const report = reports.find((item) => item.id === reportId);
    if (!report || !canRemoveReport(report)) return;
    store.reports[declarationId] = reports.filter((item) => item.id !== reportId);
    saveStore();
    renderAll();
  }

  function canRemoveReport(report) {
    return Boolean(store.currentUser && (report.user === store.currentUser || isModerator(store.currentUser)));
  }

  function isModerator(user) {
    return store.users[user]?.role === "moderator";
  }

  function makeId() {
    if (window.crypto?.randomUUID) return window.crypto.randomUUID();
    return `${Date.now()}-${Math.random().toString(16).slice(2)}`;
  }

  function readStore() {
    const base = {
      currentUser: "",
      users: {},
      conforms: {},
      reports: {},
      theme: "light",
    };
    try {
      const raw = window.localStorage.getItem(storeKey);
      if (raw) return normalizeStore({ ...base, ...JSON.parse(raw) });
    } catch {
      // Keep the default store.
    }
    return migrateOldVotes(base);
  }

  function migrateOldVotes(base) {
    try {
      const raw = window.localStorage.getItem(oldVoteKey);
      if (!raw) return base;
      const oldVotes = JSON.parse(raw);
      const conforms = {};
      for (const id of Object.keys(oldVotes || {})) {
        conforms[id] = { votes: { legacy: 1 }, updatedAt: oldVotes[id].checkedAt || new Date().toISOString() };
      }
      return normalizeStore({
        ...base,
        currentUser: "",
        users: { legacy: { createdAt: new Date().toISOString(), role: "reviewer", passwordHash: "" } },
        conforms,
      });
    } catch {
      return base;
    }
  }

  function normalizeStore(candidate) {
    const users = candidate.users && typeof candidate.users === "object" ? candidate.users : {};
    for (const [name, user] of Object.entries(users)) {
      users[name] = {
        createdAt: user?.createdAt || new Date().toISOString(),
        role: roleForUser(name),
        passwordHash: typeof user?.passwordHash === "string" ? user.passwordHash : "",
      };
    }
    return {
      currentUser: typeof candidate.currentUser === "string" ? candidate.currentUser : "",
      users,
      conforms: candidate.conforms && typeof candidate.conforms === "object" ? candidate.conforms : {},
      reports: normalizeReports(candidate.reports),
      theme: candidate.theme === "dark" ? "dark" : "light",
    };
  }

  function normalizeReports(candidate) {
    if (!candidate || typeof candidate !== "object") return {};
    const normalized = {};
    for (const [declarationId, reports] of Object.entries(candidate)) {
      if (!Array.isArray(reports)) continue;
      normalized[declarationId] = reports.map((report, index) => ({
        id: report.id || `${declarationId}:report:${index}`,
        declarationId,
        user: report.user || "unknown",
        comment: report.comment || "",
        excerpt: report.excerpt || "",
        startLine: Number(report.startLine || 0),
        endLine: Number(report.endLine || report.startLine || 0),
        createdAt: report.createdAt || new Date().toISOString(),
        replies: Array.isArray(report.replies)
          ? report.replies.map((reply, replyIndex) => ({
              id: reply.id || `${declarationId}:report:${index}:reply:${replyIndex}`,
              user: reply.user || "unknown",
              comment: reply.comment || "",
              createdAt: reply.createdAt || new Date().toISOString(),
            }))
          : [],
      }));
    }
    return normalized;
  }

  function saveStore() {
    window.localStorage.setItem(storeKey, JSON.stringify(store));
  }

  function openAccountModal() {
    els.accountName.value = store.currentUser || "";
    els.accountPassword.value = "";
    els.accountError.hidden = true;
    els.accountLogout.hidden = !store.currentUser;
    els.accountModal.hidden = false;
    requestAnimationFrame(() => (store.currentUser ? els.accountPassword : els.accountName).focus());
  }

  function closeAccountModal() {
    els.accountModal.hidden = true;
  }

  async function saveAccount(event) {
    event.preventDefault();
    const normalized = els.accountName.value.trim().replace(/\s+/g, " ");
    if (!normalized) {
      els.accountName.focus();
      return;
    }
    const password = els.accountPassword.value;
    if (!password) {
      showAccountError("Enter a password.");
      els.accountPassword.focus();
      return;
    }
    const hash = await passwordHash(normalized, password);
    const existing = store.users[normalized];
    if (existing?.passwordHash && existing.passwordHash !== hash) {
      showAccountError("The password does not match this user name.");
      els.accountPassword.focus();
      return;
    }
    const role = roleForUser(normalized);
    store.currentUser = normalized;
    store.users[normalized] = store.users[normalized] || { createdAt: new Date().toISOString(), role, passwordHash: hash };
    store.users[normalized].role = role;
    store.users[normalized].passwordHash = existing?.passwordHash || hash;
    saveStore();
    closeAccountModal();
    updateAccountUI();
    renderAll();
  }

  function logout() {
    store.currentUser = "";
    saveStore();
    closeAccountModal();
    updateAccountUI();
    renderAll();
  }

  function showAccountError(message) {
    els.accountError.textContent = message;
    els.accountError.hidden = false;
  }

  function roleForUser(user) {
    return moderatorUsernames.has(user.trim().toLowerCase()) ? "moderator" : "reviewer";
  }

  async function passwordHash(user, password) {
    const input = `${user.trim().toLowerCase()}\n${password}`;
    if (window.crypto?.subtle) {
      const bytes = new TextEncoder().encode(input);
      const digest = await window.crypto.subtle.digest("SHA-256", bytes);
      return Array.from(new Uint8Array(digest), (byte) => byte.toString(16).padStart(2, "0")).join("");
    }
    let hash = 2166136261;
    for (let index = 0; index < input.length; index += 1) {
      hash ^= input.charCodeAt(index);
      hash = Math.imul(hash, 16777619);
    }
    return `fnv1a:${(hash >>> 0).toString(16)}`;
  }

  function updateAccountUI() {
    const loggedIn = Boolean(store.currentUser);
    els.accountButton.textContent = loggedIn ? store.currentUser : "Register/Login";
    els.accountButton.title = loggedIn ? `Logged in as ${store.currentUser}` : "Guests are read-only";
    els.sourceImportButton.disabled = !loggedIn;
    els.compileButton.disabled = !loggedIn || !appState.compileAvailable;
    els.sourceImportButton.title = loggedIn ? "Import a Lean file" : "Login to import Lean files";
    els.compileButton.title = !loggedIn
      ? "Login to compile"
      : appState.compileAvailable
        ? "Run lake build at the selected node"
        : "Compile is unavailable in this deployment";
  }

  function toggleTheme() {
    store.theme = store.theme === "dark" ? "light" : "dark";
    saveStore();
    applyTheme();
  }

  function applyTheme() {
    document.body.dataset.theme = store.theme;
    els.themeToggle.textContent = store.theme === "dark" ? "Day mode" : "Night mode";
  }

  function refreshStatus() {
    // The right column is intentionally reserved for item lists only.
  }

  async function checkServer() {
    try {
      const response = await fetch("api/status", { cache: "no-store" });
      appState.serverAvailable = response.ok;
      const payload = response.ok ? await response.json() : {};
      appState.compileAvailable = Boolean(payload.compileAvailable);
    } catch {
      appState.serverAvailable = false;
      appState.compileAvailable = false;
    }
    updateAccountUI();
    refreshStatus();
  }

  async function importLeanFile(event) {
    const file = event.target.files && event.target.files[0];
    event.target.value = "";
    if (!store.currentUser) {
      showToolOutput("Login required", "Guests are read-only. Register or login to import Lean files.");
      return;
    }
    if (!file) return;
    if (!file.name.endsWith(".lean")) {
      showToolOutput("Import failed", "Choose a .lean file.");
      return;
    }

    const content = await file.text();
    const target = window.prompt("Path under the Lean root:", defaultImportPath(file.name));
    if (target === null) return;
    const normalized = normalizeLeanPath(target);
    if (!normalized) {
      showToolOutput("Import failed", "Use a relative path ending in .lean, without '..'.");
      return;
    }

    if (appState.serverAvailable) {
      try {
        const response = await fetch("api/import", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ path: normalized, content }),
        });
        const payload = await response.json();
        if (!response.ok) throw new Error(payload.error || "Import failed");
        setData(payload.data);
        showToolOutput("Imported", `${normalized} was written to ../twin-width and indexed.`);
        selectNode(normalized, "file");
        return;
      } catch (error) {
        showToolOutput("Import failed", error.message);
        return;
      }
    }

    addFileToMemory(normalized, content);
    showToolOutput("Imported in browser memory", `${normalized} was added to this page. Start the local server to write it to disk.`);
    selectNode(normalized, "file");
  }

  function defaultImportPath(fileName) {
    const selected = appState.selectedNode;
    if (!selected) return fileName;
    if (selected.type === "dir") return selected.path ? `${selected.path}/${fileName}` : fileName;
    const parts = selected.path.split("/");
    parts.pop();
    return parts.length ? `${parts.join("/")}/${fileName}` : fileName;
  }

  function normalizeLeanPath(input) {
    const normalized = input.trim().replace(/\\/g, "/").replace(/^\/+/, "");
    if (!normalized || !normalized.endsWith(".lean")) return "";
    if (normalized.split("/").some((part) => !part || part === "." || part === "..")) return "";
    return normalized;
  }

  function addFileToMemory(filePath, content) {
    const newFile = buildDataFile(filePath, content);
    const nextFiles = files.filter((file) => file.path !== filePath);
    nextFiles.push(newFile);
    const nextData = {
      ...data,
      files: nextFiles,
      fileCount: nextFiles.length,
      declarationCount: nextFiles.reduce((sum, file) => sum + file.declarations.length, 0),
      targetCount: nextFiles.reduce(
        (sum, file) => sum + file.declarations.filter((decl) => decl.votable).length,
        0,
      ),
    };
    setData(nextData);
  }

  async function compileSelectedNode() {
    const selected = appState.selectedNode;
    if (!selected) return;
    if (!store.currentUser) {
      showToolOutput("Login required", "Guests are read-only. Register or login to compile.");
      return;
    }
    if (!appState.serverAvailable) {
      showToolOutput("Compile unavailable", "Compile needs the local JS server because browsers cannot run lake build directly. Start it with: node server.js");
      return;
    }
    if (!appState.compileAvailable) {
      showToolOutput(
        "Compile unavailable",
        "This deployment does not include Lean. Use the default root Dockerfile on Render if server-side Compile is required.",
      );
      return;
    }
    showToolOutput("Compiling", `Running lake build for ${selected.path || "root"}...`);
    try {
      const response = await fetch("api/compile", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(selected),
      });
      const payload = await response.json();
      const title = payload.ok ? "Compile succeeded" : "Compile failed";
      showToolOutput(title, `$ ${payload.command}\n\n${payload.output || "(no output)"}`);
    } catch (error) {
      showToolOutput("Compile failed", error.message);
    }
  }

  function showToolOutput(title, text) {
    els.compileOutputPanel.hidden = false;
    els.toolOutput.textContent = `${title}\n${text}`;
    els.compileOutputPanel.scrollIntoView({ block: "nearest" });
  }

  function buildDataFile(filePath, content) {
    const source = content.replace(/\r\n/g, "\n");
    const lines = source.endsWith("\n") ? source.slice(0, -1).split("\n") : source.split("\n");
    return {
      path: filePath,
      module: filePath.replace(/\.lean$/, "").split("/").join("."),
      isContract: filePath.endsWith("Contract.lean"),
      isDefs: filePath.endsWith("Defs.lean"),
      lines,
      declarations: collectDeclarations(filePath, lines),
    };
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
      if (trimmed.includes(" := ") || trimmed.endsWith(" := by") || trimmed.endsWith(" where") || trimmed === "where") break;
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

  function statBadge(text) {
    const span = document.createElement("span");
    span.className = "stat-badge";
    span.textContent = text;
    return span;
  }

  function actionButton(text, className) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = className;
    button.textContent = text;
    return button;
  }

  function textSpan(className, text) {
    const span = document.createElement("span");
    span.className = className;
    span.textContent = text;
    return span;
  }

  function textBlock(tagName, text) {
    const node = document.createElement(tagName);
    node.textContent = text;
    return node;
  }

  function highlightLeanLines(lines) {
    const commentState = { inBlock: false };
    return lines.map((line) => highlightLeanLine(line, commentState));
  }

  function highlightLeanLine(line, state) {
    let output = "";
    let index = 0;
    while (index < line.length) {
      if (state.inBlock) {
        const end = line.indexOf("-/", index);
        if (end === -1) {
          output += spanHtml("tok-comment", line.slice(index));
          index = line.length;
        } else {
          output += spanHtml("tok-comment", line.slice(index, end + 2));
          state.inBlock = false;
          index = end + 2;
        }
        continue;
      }

      if (line.startsWith("/-", index)) {
        const end = line.indexOf("-/", index + 2);
        if (end === -1) {
          output += spanHtml("tok-comment", line.slice(index));
          state.inBlock = true;
          index = line.length;
        } else {
          output += spanHtml("tok-comment", line.slice(index, end + 2));
          index = end + 2;
        }
        continue;
      }

      if (line.startsWith("--", index)) {
        output += spanHtml("tok-comment", line.slice(index));
        break;
      }

      if (line[index] === '"') {
        let end = index + 1;
        while (end < line.length) {
          if (line[end] === '"' && line[end - 1] !== "\\") {
            end += 1;
            break;
          }
          end += 1;
        }
        output += spanHtml("tok-string", line.slice(index, end));
        index = end;
        continue;
      }

      const next = nextSpecialIndex(line, index);
      output += highlightCodeText(line.slice(index, next));
      index = next;
    }
    return output;
  }

  function nextSpecialIndex(line, start) {
    const candidates = [
      line.indexOf("/-", start),
      line.indexOf("--", start),
      line.indexOf('"', start),
    ].filter((item) => item !== -1);
    return candidates.length ? Math.min(...candidates) : line.length;
  }

  function highlightCodeText(text) {
    const tokenPattern = /[A-Za-z_][A-Za-z0-9_'.!?]*|\d+/g;
    let output = "";
    let cursor = 0;
    for (const match of text.matchAll(tokenPattern)) {
      output += escapeHtml(text.slice(cursor, match.index));
      const token = match[0];
      let className = "";
      if (declarationKeywords.has(token)) className = "tok-decl";
      else if (leanKeywords.has(token)) className = "tok-keyword";
      else if (/^\d+$/.test(token)) className = "tok-number";
      else if (/^(Prop|Type|Sort|Nat|Fin|Finset|Fintype|Bool|True|False)$/.test(token)) className = "tok-atom";
      else if (/^[A-Z]/.test(token)) className = "tok-type";
      output += className ? `<span class="${className}">${escapeHtml(token)}</span>` : escapeHtml(token);
      cursor = match.index + token.length;
    }
    output += escapeHtml(text.slice(cursor));
    return output;
  }

  function spanHtml(className, text) {
    return `<span class="${className}">${escapeHtml(text)}</span>`;
  }

  function highlightMatch(text) {
    const safe = escapeHtml(text || "");
    if (!appState.query) return safe;
    return safe.replace(new RegExp(escapeRegExp(appState.query), "ig"), (match) => `<mark>${match}</mark>`);
  }

  function trimDoc(doc) {
    const compact = doc.replace(/\s+/g, " ").trim();
    return compact.length > 180 ? `${compact.slice(0, 177)}...` : compact;
  }

  function escapeHtml(text) {
    return String(text)
      .replaceAll("&", "&amp;")
      .replaceAll("<", "&lt;")
      .replaceAll(">", "&gt;")
      .replaceAll('"', "&quot;");
  }

  function escapeRegExp(text) {
    return text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }
})();
