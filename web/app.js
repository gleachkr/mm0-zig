import { EditorView, keymap, highlightActiveLine, drawSelection }
  from "@codemirror/view";
import { EditorState } from "@codemirror/state";
import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { linter, setDiagnostics } from "@codemirror/lint";

const encoder = new TextEncoder();
const decoder = new TextDecoder();
const themeKey = "mm0-zig-theme";

const examples = {
  hilbert: {
    label: "hilbert",
    mm0: "./fixtures/hilbert.mm0",
    proof: "./fixtures/hilbert.proof",
  },
  hilbert_russell: {
    label: "russell",
    mm0: "./fixtures/hilbert_russell.mm0",
    proof: "./fixtures/hilbert_russell.proof",
  },
  demo_prop_cnf: {
    label: "prop cnf",
    mm0: "./fixtures/demo_prop_cnf.mm0",
    proof: "./fixtures/demo_prop_cnf.proof",
  },
  demo_nd_excluded_middle: {
    label: "nd excluded middle",
    mm0: "./fixtures/demo_nd_excluded_middle.mm0",
    proof: "./fixtures/demo_nd_excluded_middle.proof",
  },
  demo_seq_peirce: {
    label: "seq peirce",
    mm0: "./fixtures/demo_seq_peirce.mm0",
    proof: "./fixtures/demo_seq_peirce.proof",
  },
  demo_lk_exists_mono: {
    label: "lk exists mono",
    mm0: "./fixtures/demo_lk_exists_mono.mm0",
    proof: "./fixtures/demo_lk_exists_mono.proof",
  },
  quant_nd: {
    label: "quant nd",
    mm0: "./fixtures/quant_nd.mm0",
    proof: "./fixtures/quant_nd.proof",
  },
  demo_calculus_product_rule: {
    label: "calculus product rule",
    mm0: "./fixtures/demo_calculus_product_rule.mm0",
    proof: "./fixtures/demo_calculus_product_rule.proof",
  },
  demo_category_pullback: {
    label: "category pullback",
    mm0: "./fixtures/demo_category_pullback.mm0",
    proof: "./fixtures/demo_category_pullback.proof",
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
  jump: document.querySelector("#jump-button"),
  examplesBtn: document.querySelector("#examples-button"),
  exampleModal: document.querySelector("#example-modal"),
  theme: document.querySelector("#theme-toggle"),
};

let compilerModule = null;
let verifierModule = null;
let pendingTimer = null;
let lastDiagnosticSpan = null;
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
      extensions: makeExtensions("MM0 source", false),
    }),
  });

  proofView = new EditorView({
    parent: ui.proofEditor,
    state: EditorState.create({
      doc: proofText,
      extensions: makeExtensions("Proof script", true),
    }),
  });

  updateSourceMeta();

  ui.jump.addEventListener("click", jumpToProofDiagnostic);
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

  if (compileMeta?.diagnostic) {
    pushProofDiagnostic(compileMeta);
  }

  if (!compileOkay) {
    setStatus(ui.verifyStatus, "skipped", "muted");
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

function pushProofDiagnostic(meta) {
  const diag = meta.diagnostic;
  const hasSpan =
    Number.isInteger(diag.spanStart) && Number.isInteger(diag.spanEnd);
  if (!hasSpan) return;

  // The compiler returns byte offsets into UTF-8 encoded text, but CodeMirror
  // uses character offsets. Convert via encode→slice→decode.
  const text = proofView.state.doc.toString();
  const bytes = encoder.encode(text);
  const from = byteToCharPos(bytes, diag.spanStart);
  const to = Math.max(from + 1, byteToCharPos(bytes, diag.spanEnd));

  lastDiagnosticSpan = { start: from, end: to };
  ui.jump.hidden = false;

  proofView.dispatch(setDiagnostics(proofView.state, [{
    from,
    to,
    severity: "error",
    message: buildDiagnosticMessage(meta),
  }]));
}

function byteToCharPos(bytes, byteOffset) {
  const safe = Math.max(0, Math.min(byteOffset, bytes.length));
  return decoder.decode(bytes.slice(0, safe)).length;
}

function buildDiagnosticMessage(meta) {
  const parts = [meta.message];
  const diag = meta.diagnostic;
  const extra = [];
  if (diag.theorem) extra.push(diag.theorem);
  if (diag.lineLabel) extra.push(diag.lineLabel);
  if (diag.rule) extra.push(`rule ${diag.rule}`);
  if (diag.name) extra.push(diag.name);
  if (diag.expected) extra.push(`expected ${diag.expected}`);

  const detail = diag.detail;
  if (detail?.kind === "unknown_math_token" && detail.token) {
    extra.push(`token ${detail.token}`);
  } else if (
    detail?.kind === "missing_binder_assignment" &&
    detail.binder
  ) {
    extra.push(`missing binder ${detail.binder}`);
  } else if (detail?.kind === "missing_congruence_rule") {
    if (detail.summary) {
      extra.push(detail.summary);
    } else {
      const parts = [];
      if (detail.reason) parts.push(`reason ${detail.reason}`);
      if (detail.term) parts.push(`term ${detail.term}`);
      if (detail.sort) parts.push(`sort ${detail.sort}`);
      if (Number.isInteger(detail.argIndex)) {
        parts.push(`arg ${detail.argIndex + 1}`);
      }
      if (parts.length) extra.push(parts.join(" · "));
    }
  } else if (
    detail?.kind === "hypothesis_ref" &&
    Number.isInteger(detail.index)
  ) {
    extra.push(`#${detail.index}`);
  }

  if (extra.length) parts.push(extra.join(" \u00b7 "));
  return parts.join("\n");
}

function clearDiagnostics() {
  lastDiagnosticSpan = null;
  ui.jump.hidden = true;
  if (proofView) {
    proofView.dispatch(setDiagnostics(proofView.state, []));
  }
}

function jumpToProofDiagnostic() {
  if (!lastDiagnosticSpan || !proofView) return;
  setActivePane("proof");
  proofView.focus();
  proofView.dispatch({
    selection: {
      anchor: lastDiagnosticSpan.start,
      head: lastDiagnosticSpan.end,
    },
    scrollIntoView: true,
  });
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
  setStatus(ui.compileStatus, error.message, "err");
  setStatus(ui.verifyStatus, "startup failed", "err");
  ui.compileTime.textContent = "";
  ui.verifyTime.textContent = "";
  ui.mmbSize.textContent = "";
  clearDiagnostics();
}
