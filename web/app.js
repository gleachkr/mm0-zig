import { EditorView, keymap, highlightActiveLine, drawSelection }
  from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { linter, setDiagnostics } from "@codemirror/lint";

const encoder = new TextEncoder();
const decoder = new TextDecoder();
const themeKey = "aufbau-theme";

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

let compilerModule = null;
let verifierModule = null;
let pendingTimer = null;
let diagnosticStatus = null;
let diagnosticTargets = [];
let diagnosticIndex = -1;
let runToken = 0;
let mm0View = null;
let proofView = null;

initTheme();
initTabs();
initExamples();
main().catch((error) => {
  renderFatal(error);
});

function makeExtensions(ariaLabel, withLint) {
  const exts = [
    highlightActiveLine(),
    drawSelection(),
    history(),
    keymap.of([...defaultKeymap, ...historyKeymap]),
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
  if (withLint) {
    exts.push(linter(() => [], { delay: 86400000 }));
  }
  return exts;
}

function exampleFromHash() {
  const name = location.hash.replace(/^#/, "");
  return examples[name] ? name : "hilbert";
}

async function main() {
  const initial = exampleFromHash();
  const [compiler, verifier, mm0Text, proofText] = await Promise.all([
    loadWasm("./compiler.wasm"),
    loadWasm("./verifier.wasm"),
    fetchText(examples[initial].mm0),
    fetchText(examples[initial].proof),
  ]);

  compilerModule = compiler;
  verifierModule = verifier;

  mm0View = new EditorView({
    parent: ui.mm0Editor,
    state: EditorState.create({
      doc: mm0Text,
      extensions: makeExtensions("MM0 source", true),
    }),
  });

  proofView = new EditorView({
    parent: ui.proofEditor,
    state: EditorState.create({
      doc: proofText,
      extensions: makeExtensions("Aufbau script", true),
    }),
  });

  updateSourceMeta();

  ui.diagnosticPrev.addEventListener("click", () => navigateDiagnostics(-1));
  ui.diagnosticNext.addEventListener("click", () => navigateDiagnostics(1));
  for (const btn of ui.exampleButtons) {
    btn.addEventListener("click", () => loadExample(btn.dataset.example));
  }

  markActiveExample(initial);
  window.addEventListener("hashchange", () => {
    const name = exampleFromHash();
    loadExample(name);
  });

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

async function loadExample(name) {
  const example = examples[name];
  if (!example || !compilerModule || !verifierModule || !mm0View || !proofView) {
    return;
  }

  if (location.hash.replace(/^#/, "") !== name) {
    window.history.pushState(null, "", `#${name}`);
  }

  const [mm0Text, proofText] = await Promise.all([
    fetchText(example.mm0),
    fetchText(example.proof),
  ]);

  setEditorContent(mm0View, mm0Text);
  setEditorContent(proofView, proofText);
  updateSourceMeta();
  clearDiagnosticStatus();
  clearDiagnostics();

  markActiveExample(name);
  ui.exampleModal.close();

  await runAnalysis();
}

function setEditorContent(view, text) {
  view.dispatch({
    changes: { from: 0, to: view.state.doc.length, insert: text },
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
  if (!compilerModule || !verifierModule || !mm0View || !proofView) {
    return;
  }

  const token = ++runToken;
  clearDiagnosticStatus();
  setStatus(ui.compileStatus, "running…", "warn");
  setStatus(ui.verifyStatus, "waiting…", "muted");
  ui.compileTime.textContent = "";
  ui.verifyTime.textContent = "";
  ui.mmbSize.textContent = "";
  clearDiagnostics();

  const mm0Text = mm0View.state.doc.toString();
  const proofText = proofView.state.doc.toString();
  const compileResult = callCompiler(mm0Text, proofText);
  if (token !== runToken) {
    return;
  }

  const compileMeta = compileResult.meta;
  const compileDiagnostics = collectCompileDiagnostics(compileMeta);
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

  const renderedDiagnostics = pushCompileDiagnostics(compileDiagnostics);

  if (!compileOkay) {
    setDiagnosticStatus(renderedDiagnostics);
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

function clearDiagnostics() {
  diagnosticTargets = [];
  diagnosticIndex = -1;
  ui.diagnosticNav.hidden = true;
  ui.diagnosticPrev.disabled = true;
  ui.diagnosticNext.disabled = true;
  if (mm0View) {
    mm0View.dispatch(setDiagnostics(mm0View.state, []));
  }
  if (proofView) {
    proofView.dispatch(setDiagnostics(proofView.state, []));
  }
}

function callCompiler(mm0Text, proofText) {
  const module = compilerModule;
  const mm0Bytes = encoder.encode(mm0Text);
  const proofBytes = encoder.encode(proofText);
  const mm0Input = writeBytes(module, mm0Bytes);
  const proofInput = writeBytes(module, proofBytes);

  try {
    const started = performance.now();
    module.exports.compile_sources(
      mm0Input.ptr,
      mm0Input.len,
      proofInput.ptr,
      proofInput.len,
    );
    const durationMs = performance.now() - started;
    const meta = readJsonResult(module);
    const mmbBytes = meta?.ok
      ? readBytes(
          module,
          module.exports.result_mmb_ptr(),
          module.exports.result_mmb_len(),
        )
      : new Uint8Array();
    return { meta, durationMs, mmbBytes };
  } finally {
    freeBytes(module, mm0Input);
    freeBytes(module, proofInput);
  }
}

function callVerifier(mm0Text, mmbBytes) {
  const module = verifierModule;
  const mm0Bytes = encoder.encode(mm0Text);
  const mm0Input = writeBytes(module, mm0Bytes);
  const mmbInput = writeBytes(module, mmbBytes);

  try {
    const started = performance.now();
    module.exports.verify_pair(
      mm0Input.ptr,
      mm0Input.len,
      mmbInput.ptr,
      mmbInput.len,
    );
    const durationMs = performance.now() - started;
    return { meta: readJsonResult(module), durationMs };
  } finally {
    freeBytes(module, mm0Input);
    freeBytes(module, mmbInput);
  }
}

function writeBytes(module, bytes) {
  const len = bytes.length;
  const ptr = module.exports.alloc(len);
  if (len !== 0 && ptr === 0) {
    throw new Error("WebAssembly allocation failed");
  }
  if (len !== 0) {
    new Uint8Array(module.exports.memory.buffer, ptr, len).set(bytes);
  }
  return { ptr, len };
}

function freeBytes(module, { ptr, len }) {
  module.exports.free(ptr, len);
}

function readBytes(module, ptr, len) {
  if (!ptr || !len) {
    return new Uint8Array();
  }
  const view = new Uint8Array(module.exports.memory.buffer, ptr, len);
  return view.slice();
}

function readJsonResult(module) {
  const ptr = module.exports.result_json_ptr();
  const len = module.exports.result_json_len();
  if (!ptr || !len) {
    return null;
  }
  const jsonBytes = new Uint8Array(module.exports.memory.buffer, ptr, len);
  return JSON.parse(decoder.decode(jsonBytes));
}

async function loadWasm(url) {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to load ${url}`);
  }
  const bytes = await response.arrayBuffer();
  const { instance } = await WebAssembly.instantiate(bytes, {});
  return instance;
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
