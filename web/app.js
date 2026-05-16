import { EditorView, keymap, highlightActiveLine, drawSelection }
  from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { linter, setDiagnostics } from "@codemirror/lint";
import {
  LSPClient,
  jumpToDefinition,
  languageServerExtensions,
} from "@codemirror/lsp-client";
import { loadCompiler } from "@aufbau/compiler";
import { loadVerifier } from "@aufbau/verifier";
import { loadLspServer } from "@aufbau/lsp";

const encoder = new TextEncoder();
const decoder = new TextDecoder();
const themeKey = "aufbau-theme";
const mm0Uri = "file:///demo/current.mm0";
const proofUri = "file:///demo/current.auf";

const examples = {
  hilbert: {
    label: "hilbert",
    mm0: "./fixtures/hilbert.mm0",
    proof: "./fixtures/hilbert.auf",
  },
  russell: {
    label: "russell",
    mm0: "./fixtures/russell.mm0",
    proof: "./fixtures/russell.auf",
  },
  tseitin: {
    label: "tseitin",
    mm0: "./fixtures/tseitin.mm0",
    proof: "./fixtures/tseitin.auf",
  },
  robinson: {
    label: "robinson",
    mm0: "./fixtures/robinson.mm0",
    proof: "./fixtures/robinson.auf",
  },
  aristotle: {
    label: "aristotle",
    mm0: "./fixtures/aristotle.mm0",
    proof: "./fixtures/aristotle.auf",
  },
  peirce: {
    label: "peirce",
    mm0: "./fixtures/peirce.mm0",
    proof: "./fixtures/peirce.auf",
  },
  gentzen: {
    label: "gentzen",
    mm0: "./fixtures/gentzen.mm0",
    proof: "./fixtures/gentzen.auf",
  },
  prawitz: {
    label: "prawitz",
    mm0: "./fixtures/prawitz.mm0",
    proof: "./fixtures/prawitz.auf",
  },
  barcan: {
    label: "barcan",
    mm0: "./fixtures/barcan.mm0",
    proof: "./fixtures/barcan.auf",
  },
  prior: {
    label: "prior",
    mm0: "./fixtures/prior.mm0",
    proof: "./fixtures/prior.auf",
  },
  pnueli: {
    label: "pnueli",
    mm0: "./fixtures/pnueli.mm0",
    proof: "./fixtures/pnueli.auf",
  },
  barwise: {
    label: "barwise",
    mm0: "./fixtures/barwise.mm0",
    proof: "./fixtures/barwise.auf",
  },
  loeb: {
    label: "loeb",
    mm0: "./fixtures/loeb.mm0",
    proof: "./fixtures/loeb.auf",
  },
  church: {
    label: "church",
    mm0: "./fixtures/church.mm0",
    proof: "./fixtures/church.auf",
  },
  leibniz: {
    label: "leibniz",
    mm0: "./fixtures/leibniz.mm0",
    proof: "./fixtures/leibniz.auf",
  },
  mac_lane: {
    label: "mac lane",
    mm0: "./fixtures/mac_lane.mm0",
    proof: "./fixtures/mac_lane.auf",
  },
  martin_lof: {
    label: "martin-löf",
    mm0: "./fixtures/martin_lof.mm0",
    proof: "./fixtures/martin_lof.auf",
  },
  peano: {
    label: "peano",
    mm0: "./fixtures/peano.mm0",
    proof: "./fixtures/peano.auf",
  },
  euclid: {
    label: "euclid",
    mm0: "./fixtures/euclid.mm0",
    proof: "./fixtures/euclid.auf",
  },
  smullyan: {
    label: "smullyan",
    mm0: "./fixtures/smullyan.mm0",
    proof: "./fixtures/smullyan.auf",
  },
  zermelo: {
    label: "zermelo",
    mm0: "./fixtures/zermelo.mm0",
    proof: "./fixtures/zermelo.auf",
  },
};

const editorTheme = EditorView.theme({
  "&": {
    height: "100%",
    background: "transparent",
    color: "var(--text)",
  },
  ".cm-scroller": {
    fontFamily:
      '"Fira Code", "FiraCode Nerd Font", "Fira Mono", '
      + '"IBM Plex Mono", ui-monospace, monospace',
    fontFeatureSettings: '"calt" 1, "liga" 1',
    lineHeight: "1.65",
    fontSize: "14px",
    overflow: "auto",
    minHeight: "0",
  },
  ".cm-content": {
    padding: "1rem 0 6rem",
    caretColor: "var(--accent)",
  },
  ".cm-line": {
    padding: "0 1.25rem",
  },
  ".cm-gutters": {
    background: "transparent",
    border: "none",
    color: "var(--muted)",
    paddingLeft: "0.5rem",
  },
  ".cm-activeLineGutter": {
    background: "transparent",
  },
  ".cm-activeLine": {
    background: "var(--panel-muted)",
  },
  "&.cm-focused .cm-selectionBackground, .cm-selectionBackground": {
    background: "var(--selection) !important",
  },
  ".cm-cursor, .cm-dropCursor": {
    borderLeftColor: "var(--accent)",
  },
  "&.cm-focused": {
    outline: "none",
  },
  ".cm-lintRange-error": {
    backgroundImage: "none",
    textDecoration: "underline wavy var(--err)",
    textUnderlineOffset: "3px",
  },
  ".cm-lintRange-warning": {
    backgroundImage: "none",
    textDecoration: "underline wavy var(--warn)",
    textUnderlineOffset: "3px",
  },
  ".cm-tooltip": {
    background: "var(--bubble)",
    border: "1px solid rgb(255 255 255 / 0.12)",
    borderRadius: "0.8rem",
    boxShadow: "0 14px 38px rgb(0 0 0 / 0.22)",
  },
  ".cm-tooltip-lint": {
    padding: "0",
  },
  ".cm-diagnostic": {
    padding: "0.52rem 0.72rem",
    borderLeft: "none",
    color: "#fff6f6",
    whiteSpace: "pre-wrap",
    fontFamily:
      '"Fira Code", "FiraCode Nerd Font", "Fira Mono", '
      + '"IBM Plex Mono", ui-monospace, monospace',
    fontSize: "13px",
  },
  ".cm-diagnostic-error": {
    borderLeft: "none",
  },
  ".cm-diagnostic-warning": {
    borderLeft: "none",
    color: "#fff8e3",
  },
});

const ui = {
  mm0Editor: document.querySelector("#mm0-editor"),
  proofEditor: document.querySelector("#proof-editor"),
  panes: [...document.querySelectorAll(".pane")],
  tabs: [...document.querySelectorAll("[data-pane-tab]")],
  exampleButtons: [...document.querySelectorAll("[data-example]")],
  mm0Meta: document.querySelector("#mm0-meta"),
  proofMeta: document.querySelector("#proof-meta"),
  compileStatus: document.querySelector("#compile-status"),
  compileTime: document.querySelector("#compile-time"),
  mmbSize: document.querySelector("#mmb-size"),
  verifyStatus: document.querySelector("#verify-status"),
  verifyTime: document.querySelector("#verify-time"),
  diagnosticNav: document.querySelector("#diagnostic-nav"),
  diagnosticPrev: document.querySelector("#diagnostic-prev"),
  diagnosticNext: document.querySelector("#diagnostic-next"),
  examplesBtn: document.querySelector("#examples-button"),
  exampleModal: document.querySelector("#example-modal"),
  theme: document.querySelector("#theme-toggle"),
};

let compilerRuntime = null;
let verifierRuntime = null;
let pendingTimer = null;
let diagnosticStatus = null;
let diagnosticTargets = [];
let diagnosticIndex = -1;
let runToken = 0;
let mm0View = null;
let proofView = null;
let lspClient = null;
let lspServer = null;
let currentExample = null;
let currentRouteKey = null;

initTheme();
initTabs();
initExamples();
main().catch((error) => {
  renderFatal(error);
});

function makeExtensions(ariaLabel, withLint, lspExtension) {
  const exts = [
    highlightActiveLine(),
    drawSelection(),
    history(),
    keymap.of([
      {
        key: "Ctrl-]",
        run: jumpToDefinition,
        preventDefault: true,
      },
      ...defaultKeymap,
      ...historyKeymap,
    ]),
    EditorView.updateListener.of((update) => {
      if (update.docChanged) scheduleRun();
    }),
    EditorView.contentAttributes.of({
      "aria-label": ariaLabel,
      spellcheck: "false",
    }),
    editorTheme,
    EditorState.tabSize.of(2),
  ];
  if (lspExtension) {
    exts.push(lspExtension);
  }
  if (withLint) {
    exts.push(linter(() => [], { delay: 86400000 }));
  }
  return exts;
}

function routeFromHash() {
  const raw = location.hash.replace(/^#/, "");
  const slash = raw.indexOf("/");
  const rawExample = slash < 0 ? raw : raw.slice(0, slash);
  const rawTheorem = slash < 0 ? "" : raw.slice(slash + 1);
  const name = safeDecode(rawExample);
  const theorem = rawTheorem ? safeDecode(rawTheorem) : null;
  return {
    example: examples[name] ? name : "hilbert",
    theorem,
  };
}

function safeDecode(value) {
  try {
    return decodeURIComponent(value);
  } catch {
    return value;
  }
}

function routeHash(name, theorem) {
  const parts = [encodeURIComponent(name)];
  if (theorem) parts.push(encodeURIComponent(theorem));
  return `#${parts.join("/")}`;
}

function pushRoute(name, theorem) {
  const next = routeHash(name, theorem);
  if (location.hash !== next) {
    window.history.pushState(null, "", next);
  }
}

async function main() {
  const initialRoute = routeFromHash();
  const initial = initialRoute.example;
  const [compiler, verifier, server, mm0Text, proofText] = await Promise.all([
    loadCompiler(),
    loadVerifier(),
    loadLspServer(),
    fetchText(examples[initial].mm0),
    fetchText(examples[initial].proof),
  ]);

  compilerRuntime = compiler;
  verifierRuntime = verifier;
  lspServer = server;
  lspClient = new LSPClient({
    rootUri: "file:///demo",
    extensions: languageServerExtensions(),
  }).connect(lspServer);

  mm0View = new EditorView({
    parent: ui.mm0Editor,
    state: EditorState.create({
      doc: mm0Text,
      extensions: makeExtensions(
        "MM0 source",
        true,
        lspClient.plugin(mm0Uri, "mm0"),
      ),
    }),
  });

  proofView = new EditorView({
    parent: ui.proofEditor,
    state: EditorState.create({
      doc: proofText,
      extensions: makeExtensions(
        "Aufbau script",
        true,
        lspClient.plugin(proofUri, "aufbau"),
      ),
    }),
  });

  updateSourceMeta();

  ui.diagnosticPrev.addEventListener("click", () => navigateDiagnostics(-1));
  ui.diagnosticNext.addEventListener("click", () => navigateDiagnostics(1));
  for (const btn of ui.exampleButtons) {
    btn.addEventListener("click", () => loadExample(btn.dataset.example));
  }

  currentExample = initial;
  currentRouteKey = routeHash(initial, initialRoute.theorem);
  markActiveExample(initial);
  revealTheoremFromRoute(initialRoute.theorem);
  window.addEventListener("hashchange", handleRouteChange);
  window.addEventListener("popstate", handleRouteChange);

  warmUpAnalysis(mm0Text, proofText);
  await runAnalysis();
}

function markActiveExample(name) {
  const example = examples[name];
  if (!example) return;
  for (const btn of ui.exampleButtons) {
    const active = btn.dataset.example === name;
    btn.classList.toggle("is-active", active);
    btn.setAttribute("aria-pressed", String(active));
  }
  ui.examplesBtn.textContent = example.label;
}

async function handleRouteChange() {
  const route = routeFromHash();
  const routeKey = routeHash(route.example, route.theorem);
  if (routeKey === currentRouteKey) return;
  currentRouteKey = routeKey;

  if (route.example === currentExample) {
    revealTheoremFromRoute(route.theorem);
    return;
  }
  await loadExample(route.example, {
    theorem: route.theorem,
    updateHash: false,
  });
}

async function loadExample(name, options = {}) {
  const example = examples[name];
  if (!example || !compilerRuntime || !verifierRuntime || !mm0View || !proofView) {
    return;
  }

  if (options.updateHash !== false) {
    pushRoute(name, options.theorem ?? null);
  }

  const [mm0Text, proofText] = await Promise.all([
    fetchText(example.mm0),
    fetchText(example.proof),
  ]);

  setEditorContent(mm0View, mm0Text);
  setEditorContent(proofView, proofText);
  lspClient?.sync();
  updateSourceMeta();
  clearDiagnosticStatus();
  clearDiagnostics();

  currentExample = name;
  currentRouteKey = routeHash(name, options.theorem ?? null);
  markActiveExample(name);
  revealTheoremFromRoute(options.theorem ?? null);
  ui.exampleModal.close();

  await runAnalysis();
}

function setEditorContent(view, text) {
  view.dispatch({
    changes: { from: 0, to: view.state.doc.length, insert: text },
  });
}

function revealTheoremFromRoute(name) {
  if (!name) return;
  if (revealProofBlock(name)) return;
  if (revealMm0Assertion(name)) return;
  console.warn(`No theorem named ${name} in ${currentExample}`);
}

function revealProofBlock(name) {
  if (!proofView) return false;
  const range = findProofBlock(proofView, name);
  if (!range) return false;
  focusRange("proof", proofView, range);
  return true;
}

function revealMm0Assertion(name) {
  if (!mm0View) return false;
  const range = findMm0Assertion(mm0View, name);
  if (!range) return false;
  focusRange("mm0", mm0View, range);
  return true;
}

function findProofBlock(view, name) {
  const doc = view.state.doc;
  for (let i = 1; i <= doc.lines; i += 1) {
    const line = doc.line(i);
    const trimmed = line.text.trim();
    if (trimmed === name && isProofUnderline(doc, i + 1)) {
      return rangeForName(line, name);
    }

    const lemma = line.text.match(/^\s*lemma\s+([A-Za-z_][A-Za-z0-9_']*)\b/);
    if (lemma?.[1] === name) {
      return rangeForName(line, name);
    }
  }
  return null;
}

function isProofUnderline(doc, lineNumber) {
  if (lineNumber > doc.lines) return false;
  return /^-+\s*$/.test(doc.line(lineNumber).text);
}

function findMm0Assertion(view, name) {
  const doc = view.state.doc;
  const pattern = /^\s*(?:(?:pub|local)\s+)?(?:axiom|theorem|lemma)\s+/;
  for (let i = 1; i <= doc.lines; i += 1) {
    const line = doc.line(i);
    if (!pattern.test(line.text)) continue;
    const assertion = line.text.slice(line.text.search(pattern));
    const match = assertion.match(
      /^\s*(?:(?:pub|local)\s+)?(?:axiom|theorem|lemma)\s+([^\s({:]+)/,
    );
    if (match?.[1] === name) {
      return rangeForName(line, name);
    }
  }
  return null;
}

function rangeForName(line, name) {
  const column = line.text.indexOf(name);
  const from = line.from + Math.max(column, 0);
  return { from, to: from + name.length };
}

function focusRange(pane, view, range) {
  setActivePane(pane);
  view.focus();
  view.dispatch({
    selection: {
      anchor: range.from,
      head: range.to,
    },
    effects: EditorView.scrollIntoView(range.from, {
      y: "start",
      yMargin: 16,
    }),
  });
}

function initTheme() {
  const theme = getStoredTheme() ?? getPreferredTheme();
  applyTheme(theme);
  ui.theme.addEventListener("click", toggleTheme);
}

function initTabs() {
  for (const tab of ui.tabs) {
    tab.addEventListener("click", () => {
      setActivePane(tab.dataset.paneTab);
    });
  }
}

function initExamples() {
  ui.examplesBtn.addEventListener("click", () => ui.exampleModal.showModal());
  ui.exampleModal.addEventListener("click", (e) => {
    if (e.target === ui.exampleModal) ui.exampleModal.close();
  });
  document.querySelector("#modal-close").addEventListener("click", () => {
    ui.exampleModal.close();
  });
}

function getStoredTheme() {
  try {
    const value = localStorage.getItem(themeKey);
    return value === "light" || value === "dark" ? value : null;
  } catch {
    return null;
  }
}

function getPreferredTheme() {
  return window.matchMedia("(prefers-color-scheme: light)").matches
    ? "light"
    : "dark";
}

function applyTheme(theme) {
  document.documentElement.dataset.theme = theme;
  ui.theme.textContent = theme === "dark" ? "light" : "dark";
  ui.theme.setAttribute(
    "aria-label",
    theme === "dark" ? "Switch to light mode" : "Switch to dark mode",
  );
  try {
    localStorage.setItem(themeKey, theme);
  } catch {
    // Ignore localStorage failures.
  }
}

function toggleTheme() {
  const current = document.documentElement.dataset.theme === "light"
    ? "light"
    : "dark";
  applyTheme(current === "dark" ? "light" : "dark");
}

function setActivePane(name) {
  for (const pane of ui.panes) {
    pane.classList.toggle("is-active", pane.dataset.pane === name);
  }
  for (const tab of ui.tabs) {
    const active = tab.dataset.paneTab === name;
    tab.classList.toggle("is-active", active);
    tab.setAttribute("aria-selected", String(active));
  }
}

function updateSourceMeta() {
  if (!mm0View || !proofView) return;
  ui.mm0Meta.textContent = formatBytes(
    encoder.encode(mm0View.state.doc.toString()).length,
  );
  ui.proofMeta.textContent = formatBytes(
    encoder.encode(proofView.state.doc.toString()).length,
  );
}

function scheduleRun() {
  updateSourceMeta();
  clearTimeout(pendingTimer);
  pendingTimer = setTimeout(() => {
    void runAnalysis();
  }, 250);
}

function warmUpAnalysis(mm0Text, proofText) {
  try {
    const compileResult = callCompiler(mm0Text, proofText);
    if (compileResult.meta?.ok) {
      callVerifier(mm0Text, compileResult.mmbBytes);
    }
  } catch (error) {
    console.warn("Warm-up run failed", error);
  }
}

async function runAnalysis() {
  if (!compilerRuntime || !verifierRuntime || !mm0View || !proofView) {
    return;
  }

  const token = ++runToken;
  lspClient?.sync();
  clearDiagnosticStatus();
  setStatus(ui.compileStatus, "running…", "warn");
  setStatus(ui.verifyStatus, "waiting…", "muted");
  ui.compileTime.textContent = "";
  ui.verifyTime.textContent = "";
  ui.mmbSize.textContent = "";
  clearDiagnosticNavigation();

  const mm0Text = mm0View.state.doc.toString();
  const proofText = proofView.state.doc.toString();
  const compileResult = callCompiler(mm0Text, proofText);
  if (token !== runToken) {
    return;
  }

  const compileMeta = compileResult.meta;
  const compileOkay = Boolean(compileMeta?.ok);
  setStatus(
    ui.compileStatus,
    compileOkay ? "ok" : compileMeta?.message || "compile failed",
    compileOkay ? "ok" : "err",
  );
  ui.compileTime.textContent = formatApproxMs(compileResult.durationMs);
  ui.mmbSize.textContent = compileOkay
    ? formatBytes(compileResult.mmbBytes.length)
    : "";

  if (!compileOkay) {
    setStatus(ui.verifyStatus, "compile failed", "err");
    return;
  }

  const verifyResult = callVerifier(mm0Text, compileResult.mmbBytes);
  if (token !== runToken) {
    return;
  }

  const verifyMeta = verifyResult.meta;
  const verifyOkay = Boolean(verifyMeta?.ok);
  setStatus(
    ui.verifyStatus,
    verifyOkay ? "ok" : verifyMeta?.message || "verify failed",
    verifyOkay ? "ok" : "err",
  );
  ui.verifyTime.textContent = formatApproxMs(verifyResult.durationMs);
}

function pushCompileDiagnostics(diagnostics) {
  if (!mm0View || !proofView) return [];

  const rendered = renderCompileDiagnostics(diagnostics);
  mm0View.dispatch(setDiagnostics(mm0View.state, rendered.mm0Diagnostics));
  proofView.dispatch(setDiagnostics(proofView.state, rendered.proofDiagnostics));

  diagnosticTargets = rendered.targets;
  diagnosticIndex = -1;
  updateDiagnosticNavigation();
  return rendered.targets;
}

function collectCompileDiagnostics(meta) {
  if (Array.isArray(meta?.diagnostics)) {
    return meta.diagnostics;
  }
  if (meta?.diagnostic) {
    return [meta.diagnostic];
  }
  return [];
}

function renderCompileDiagnostics(diagnostics) {
  const rendered = {
    mm0Diagnostics: [],
    proofDiagnostics: [],
    targets: [],
  };

  for (const diag of diagnostics) {
    const target = compileDiagnosticTarget(diag);
    if (!target) continue;

    const editorDiag = {
      from: target.from,
      to: target.to,
      severity: target.severity,
      message: buildDiagnosticMessage(diag),
    };
    if (target.pane === "mm0") {
      rendered.mm0Diagnostics.push(editorDiag);
    } else {
      rendered.proofDiagnostics.push(editorDiag);
    }
    rendered.targets.push(target);
  }

  return rendered;
}

function compileDiagnosticTarget(diag) {
  const severity = diag?.severity === "warning" ? "warning" : "error";
  if (diag?.source === "mm0") {
    const range = diagnosticRange(mm0View, diag);
    return range ? { pane: "mm0", severity, ...range } : null;
  }
  if (diag?.source === "proof") {
    const range = diagnosticRange(proofView, diag);
    return range ? { pane: "proof", severity, ...range } : null;
  }
  return null;
}

function updateDiagnosticNavigation() {
  const count = diagnosticTargets.length;
  ui.diagnosticNav.hidden = count === 0;
  ui.diagnosticPrev.disabled = count === 0;
  ui.diagnosticNext.disabled = count === 0;
  updateDiagnosticStatus();
}

function navigateDiagnostics(delta) {
  const count = diagnosticTargets.length;
  if (count === 0) return;

  if (diagnosticIndex < 0) {
    diagnosticIndex = delta >= 0 ? 0 : count - 1;
  } else {
    diagnosticIndex = (diagnosticIndex + delta + count) % count;
  }

  focusDiagnostic(diagnosticTargets[diagnosticIndex]);
  updateDiagnosticNavigation();
}

function focusDiagnostic(target) {
  const view = target.pane === "mm0" ? mm0View : proofView;
  if (!view) return;

  setActivePane(target.pane);
  view.focus();
  view.dispatch({
    selection: {
      anchor: target.from,
      head: target.to,
    },
    scrollIntoView: true,
  });
}

function diagnosticCounts(diagnostics) {
  const counts = { error: 0, warning: 0 };
  for (const diag of diagnostics) {
    if (diag?.severity === "warning") {
      counts.warning += 1;
    } else {
      counts.error += 1;
    }
  }
  return counts;
}

function formatDiagnosticCountSummary(diagnostics) {
  const counts = diagnosticCounts(diagnostics);
  const parts = [];
  if (counts.error !== 0) {
    parts.push(formatCount(counts.error, "error"));
  }
  if (counts.warning !== 0) {
    parts.push(formatCount(counts.warning, "warning"));
  }
  return parts.join(", ");
}

function diagnosticStatusKind(diagnostics) {
  const counts = diagnosticCounts(diagnostics);
  if (counts.error !== 0) return "err";
  if (counts.warning !== 0) return "warn";
  return "muted";
}

function setDiagnosticStatus(diagnostics) {
  const summary = formatDiagnosticCountSummary(diagnostics);
  if (!summary) {
    clearDiagnosticStatus();
    setStatus(ui.verifyStatus, "compile failed", "err");
    return;
  }
  diagnosticStatus = {
    summary,
    kind: diagnosticStatusKind(diagnostics),
  };
  updateDiagnosticStatus();
}

function clearDiagnosticStatus() {
  diagnosticStatus = null;
}

function updateDiagnosticStatus() {
  if (!diagnosticStatus) return;
  const position = formatDiagnosticPosition();
  const text = position
    ? `${diagnosticStatus.summary} (${position})`
    : diagnosticStatus.summary;
  setStatus(ui.verifyStatus, text, diagnosticStatus.kind);
}

function formatDiagnosticPosition() {
  const count = diagnosticTargets.length;
  if (count === 0) return null;
  const current = diagnosticIndex < 0 ? 0 : diagnosticIndex + 1;
  return `${current}/${count}`;
}

function formatCount(count, label) {
  return `${count} ${label}${count === 1 ? "" : "s"}`;
}

function diagnosticRange(view, diag) {
  if (!view) return null;
  const hasSpan =
    Number.isInteger(diag?.spanStart) && Number.isInteger(diag?.spanEnd);
  if (!hasSpan) return null;

  // The compiler returns byte offsets into UTF-8 encoded text, but CodeMirror
  // uses character offsets. Convert via encode→slice→decode.
  const text = view.state.doc.toString();
  const bytes = encoder.encode(text);
  const from = byteToCharPos(bytes, diag.spanStart);
  const to = Math.max(from + 1, byteToCharPos(bytes, diag.spanEnd));
  return { from, to };
}

function byteToCharPos(bytes, byteOffset) {
  const safe = Math.max(0, Math.min(byteOffset, bytes.length));
  return decoder.decode(bytes.slice(0, safe)).length;
}

function buildDiagnosticMessage(diag) {
  const parts = [diag.message || diag.error || "diagnostic"];
  const context = [];
  if (diag.theorem) context.push(diag.theorem);
  if (diag.block && diag.block !== diag.theorem) context.push(diag.block);
  if (diag.lineLabel) context.push(diag.lineLabel);
  if (diag.rule) context.push(`rule ${diag.rule}`);
  if (diag.name) context.push(diag.name);
  if (diag.expected) context.push(`expected ${diag.expected}`);
  if (diag.phase) context.push(`phase ${humanizeDiagnosticValue(diag.phase)}`);
  if (context.length) parts.push(context.join(" · "));

  const detail = buildDiagnosticDetail(diag.detail);
  if (detail) parts.push(detail);

  if (Array.isArray(diag.notes)) {
    for (const note of diag.notes) {
      const source = note?.source ? ` (${note.source})` : "";
      if (note?.message) parts.push(`note${source}: ${note.message}`);
    }
  }

  if (Array.isArray(diag.related)) {
    for (const related of diag.related) {
      const source = related?.source ? ` (${related.source})` : "";
      if (related?.label) parts.push(`related${source}: ${related.label}`);
    }
  }

  return parts.join("\n");
}

function buildDiagnosticDetail(detail) {
  if (!detail?.kind) return "";

  if (detail.summary) return detail.summary;

  if (detail.kind === "unknown_math_token" && detail.token) {
    return `token ${detail.token}`;
  }

  if (detail.kind === "missing_binder_assignment") {
    const parts = [];
    if (detail.binder) parts.push(`missing binder ${detail.binder}`);
    if (detail.path) parts.push(`path ${humanizeDiagnosticValue(detail.path)}`);
    return parts.join(" · ");
  }

  if (detail.kind === "inference_failure") {
    const parts = [];
    if (detail.path) parts.push(`path ${humanizeDiagnosticValue(detail.path)}`);
    if (detail.firstUnsolvedBinder) {
      parts.push(`first unsolved binder ${detail.firstUnsolvedBinder}`);
    }
    return parts.join(" · ");
  }

  if (detail.kind === "missing_congruence_rule") {
    const parts = [];
    if (detail.reason) parts.push(`reason ${humanizeDiagnosticValue(detail.reason)}`);
    if (detail.term) parts.push(`term ${detail.term}`);
    if (detail.sort) parts.push(`sort ${detail.sort}`);
    if (Number.isInteger(detail.argIndex)) {
      parts.push(`arg ${detail.argIndex + 1}`);
    }
    return parts.join(" · ");
  }

  if (detail.kind === "dep_violation") {
    const parts = [];
    if (detail.firstArgName && detail.secondArgName) {
      parts.push(
        `conflicting binders ${detail.firstArgName} and ${detail.secondArgName}`,
      );
    }
    if (Number.isInteger(detail.firstDeps)) {
      parts.push(`first deps 0x${detail.firstDeps.toString(16)}`);
    }
    if (Number.isInteger(detail.secondDeps)) {
      parts.push(`second deps 0x${detail.secondDeps.toString(16)}`);
    }
    return parts.join(" · ");
  }

  if (detail.kind === "hypothesis_ref" && Number.isInteger(detail.index)) {
    return `#${detail.index}`;
  }

  if (detail.kind === "unused_parameter" && detail.parameter) {
    return `parameter ${detail.parameter}`;
  }

  if (detail.kind === "omitted_diagnostics" && Number.isInteger(detail.count)) {
    return `${detail.count} more diagnostics omitted`;
  }

  return "";
}

function humanizeDiagnosticValue(value) {
  return String(value).replaceAll("_", " ");
}

function clearDiagnosticNavigation() {
  diagnosticTargets = [];
  diagnosticIndex = -1;
  ui.diagnosticNav.hidden = true;
  ui.diagnosticPrev.disabled = true;
  ui.diagnosticNext.disabled = true;
}

function clearDiagnostics() {
  clearDiagnosticNavigation();
  if (mm0View) {
    mm0View.dispatch(setDiagnostics(mm0View.state, []));
  }
  if (proofView) {
    proofView.dispatch(setDiagnostics(proofView.state, []));
  }
}

function callCompiler(mm0Text, proofText) {
  if (!compilerRuntime) throw new Error("compiler is not loaded");
  return compilerRuntime.compile(mm0Text, proofText);
}

function callVerifier(mm0Text, mmbBytes) {
  if (!verifierRuntime) throw new Error("verifier is not loaded");
  return verifierRuntime.verifyPair(mm0Text, mmbBytes);
}

async function fetchText(url) {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to load ${url}`);
  }
  return response.text();
}

function setStatus(node, text, kind) {
  node.textContent = text;
  node.className = `status ${kind}`;
}

function formatApproxMs(value) {
  if (!Number.isFinite(value)) {
    return "";
  }
  if (value < 1) {
    return `\u2248 ${value.toFixed(1)} ms`;
  }
  if (value < 10) {
    return `\u2248 ${value.toFixed(1)} ms`;
  }
  return `\u2248 ${Math.round(value)} ms`;
}

function formatBytes(value) {
  if (value < 1024) {
    return `${value} B`;
  }
  if (value < 1024 * 1024) {
    return `${(value / 1024).toFixed(1)} KiB`;
  }
  return `${(value / (1024 * 1024)).toFixed(2)} MiB`;
}

function renderFatal(error) {
  clearDiagnosticStatus();
  setStatus(ui.compileStatus, error.message, "err");
  setStatus(ui.verifyStatus, "startup failed", "err");
  ui.compileTime.textContent = "";
  ui.verifyTime.textContent = "";
  ui.mmbSize.textContent = "";
  clearDiagnostics();
}
