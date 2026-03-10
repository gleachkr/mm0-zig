const encoder = new TextEncoder();
const decoder = new TextDecoder();
const themeKey = "mm0-zig-theme";
const measureCanvas = document.createElement("canvas");
const measureContext = measureCanvas.getContext("2d");

const examples = {
  hilbert: {
    mm0: "./fixtures/hilbert.mm0",
    proof: "./fixtures/hilbert.proof",
  },
  hilbert_russell: {
    mm0: "./fixtures/hilbert_russell.mm0",
    proof: "./fixtures/hilbert_russell.proof",
  },
};

const ui = {
  mm0: document.querySelector("#mm0-source"),
  proof: document.querySelector("#proof-source"),
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
  proofShell: document.querySelector("#proof-shell"),
  inlineHighlight: document.querySelector("#proof-inline-highlight"),
  inlineBubble: document.querySelector("#proof-inline-bubble"),
  inlineMessage: document.querySelector("#proof-inline-message"),
  inlineMeta: document.querySelector("#proof-inline-meta"),
};

let compilerModule = null;
let verifierModule = null;
let pendingTimer = null;
let lastDiagnostic = null;
let runToken = 0;

initTheme();
initTabs();
initExamples();
main().catch((error) => {
  renderFatal(error);
});

document.fonts?.ready.then(() => {
  updateInlineDiagnosticPosition();
});
window.addEventListener("resize", updateInlineDiagnosticPosition);

async function main() {
  const [compiler, verifier, mm0Text, proofText] = await Promise.all([
    loadWasm("./compiler.wasm"),
    loadWasm("./verifier.wasm"),
    fetchText(examples.hilbert.mm0),
    fetchText(examples.hilbert.proof),
  ]);

  compilerModule = compiler;
  verifierModule = verifier;
  ui.mm0.value = mm0Text;
  ui.proof.value = proofText;
  updateSourceMeta();

  ui.mm0.addEventListener("input", scheduleRun);
  ui.proof.addEventListener("input", scheduleRun);
  ui.proof.addEventListener("scroll", updateInlineDiagnosticPosition);
  ui.jump.addEventListener("click", jumpToProofDiagnostic);
  for (const btn of ui.exampleButtons) {
    btn.addEventListener("click", () => loadExample(btn.dataset.example));
  }

  warmUpAnalysis(mm0Text, proofText);
  await runAnalysis();
}

async function loadExample(name) {
  const example = examples[name];
  if (!example || !compilerModule || !verifierModule) {
    return;
  }

  const [mm0Text, proofText] = await Promise.all([
    fetchText(example.mm0),
    fetchText(example.proof),
  ]);

  ui.mm0.value = mm0Text;
  ui.proof.value = proofText;
  updateSourceMeta();
  clearInlineDiagnostic();

  for (const btn of ui.exampleButtons) {
    const active = btn.dataset.example === name;
    btn.classList.toggle("is-active", active);
    btn.setAttribute("aria-pressed", String(active));
  }
  ui.examplesBtn.textContent = name;
  ui.exampleModal.close();

  await runAnalysis();
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
  updateInlineDiagnosticPosition();
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
  ui.mm0Meta.textContent = formatBytes(encoder.encode(ui.mm0.value).length);
  ui.proofMeta.textContent = formatBytes(
    encoder.encode(ui.proof.value).length,
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
  if (!compilerModule || !verifierModule) {
    return;
  }

  const token = ++runToken;
  setStatus(ui.compileStatus, "running…", "warn");
  setStatus(ui.verifyStatus, "waiting…", "muted");
  ui.compileTime.textContent = "";
  ui.verifyTime.textContent = "";
  ui.mmbSize.textContent = "";
  clearInlineDiagnostic();

  const compileResult = callCompiler(ui.mm0.value, ui.proof.value);
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
    renderInlineDiagnostic(buildProofDiagnostic(compileMeta));
  }

  if (!compileOkay) {
    setStatus(ui.verifyStatus, "skipped", "muted");
    return;
  }

  const verifyResult = callVerifier(ui.mm0.value, compileResult.mmbBytes);
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

function renderInlineDiagnostic(item) {
  lastDiagnostic = item;
  ui.jump.hidden = !item?.span;
  if (!item?.span) {
    clearInlineDiagnostic();
    return;
  }

  ui.inlineMessage.textContent = item.message;
  ui.inlineMeta.textContent = buildInlineMeta(item);
  ui.inlineMeta.hidden = ui.inlineMeta.textContent.length === 0;
  ui.inlineHighlight.hidden = false;
  ui.inlineBubble.hidden = false;
  updateInlineDiagnosticPosition();
}

function clearInlineDiagnostic() {
  lastDiagnostic = null;
  ui.jump.hidden = true;
  ui.inlineHighlight.hidden = true;
  ui.inlineBubble.hidden = true;
}

function buildInlineMeta(item) {
  const fields = [];
  if (item.line) {
    fields.push(`L${item.line}:${item.column}`);
  }
  if (item.theorem) {
    fields.push(item.theorem);
  }
  if (item.lineLabel) {
    fields.push(item.lineLabel);
  }
  if (item.rule) {
    fields.push(`rule ${item.rule}`);
  }
  if (item.name) {
    fields.push(item.name);
  }
  if (item.expected) {
    fields.push(`expected ${item.expected}`);
  }
  return fields.join(" · ");
}

function updateInlineDiagnosticPosition() {
  if (!lastDiagnostic?.span || !lastDiagnostic.line) {
    return;
  }

  const metrics = getEditorMetrics(ui.proof);
  const top =
    metrics.paddingTop +
    (lastDiagnostic.line - 1) * metrics.lineHeight -
    ui.proof.scrollTop;

  if (top + metrics.lineHeight < 0 || top > ui.proof.clientHeight) {
    ui.inlineHighlight.hidden = true;
    ui.inlineBubble.hidden = true;
    return;
  }

  ui.inlineHighlight.hidden = false;
  ui.inlineBubble.hidden = false;

  ui.inlineHighlight.style.top = `${Math.round(top)}px`;
  ui.inlineHighlight.style.height = `${Math.ceil(metrics.lineHeight)}px`;

  const bubbleHeight = ui.inlineBubble.offsetHeight || 0;
  const bubbleWidth = ui.inlineBubble.offsetWidth || 0;
  const lineWidth = measureTextWidth(ui.proof, lastDiagnostic.lineText || "");
  const idealLeft =
    metrics.paddingLeft + lineWidth + metrics.charWidth * 3 -
    ui.proof.scrollLeft;
  const maxLeft = Math.max(12, ui.proof.clientWidth - bubbleWidth - 12);
  const left = clamp(idealLeft, 12, maxLeft);
  const maxTop = Math.max(8, ui.proof.clientHeight - bubbleHeight - 8);
  const bubbleTop = clamp(top - 6, 8, maxTop);

  ui.inlineBubble.style.left = `${Math.round(left)}px`;
  ui.inlineBubble.style.top = `${Math.round(bubbleTop)}px`;
}

function getEditorMetrics(textarea) {
  const style = getComputedStyle(textarea);
  return {
    lineHeight: parseFloat(style.lineHeight),
    paddingTop: parseFloat(style.paddingTop),
    paddingLeft: parseFloat(style.paddingLeft),
    charWidth: measureCharWidth(style),
  };
}

function measureTextWidth(textarea, text) {
  const style = getComputedStyle(textarea);
  const tabSize = Number.parseInt(style.tabSize, 10) || 2;
  return countColumns(text, tabSize) * measureCharWidth(style);
}

function measureCharWidth(style) {
  if (!measureContext) {
    return 8;
  }
  measureContext.font = makeCanvasFont(style);
  return measureContext.measureText("0").width;
}

function makeCanvasFont(style) {
  const parts = [
    style.fontStyle,
    style.fontVariant,
    style.fontWeight,
    style.fontSize,
    style.fontFamily,
  ].filter(Boolean);
  return parts.join(" ");
}

function countColumns(text, tabSize) {
  let column = 0;
  for (const char of text) {
    if (char === "\t") {
      column += tabSize - (column % tabSize || 0);
    } else {
      column += 1;
    }
  }
  return column;
}

function clamp(value, min, max) {
  return Math.min(max, Math.max(min, value));
}

function buildProofDiagnostic(meta) {
  const diag = meta.diagnostic;
  const span =
    Number.isInteger(diag.spanStart) && Number.isInteger(diag.spanEnd)
      ? { start: diag.spanStart, end: diag.spanEnd }
      : null;
  const location = span
    ? offsetToLocation(ui.proof.value, span.start, span.end)
    : { line: null, column: null, lineText: null };

  return {
    message: meta.message,
    theorem: diag.theorem,
    block: diag.block,
    lineLabel: diag.lineLabel,
    rule: diag.rule,
    name: diag.name,
    expected: diag.expected,
    line: location.line ?? 0,
    column: location.column ?? 0,
    lineText: location.lineText,
    span,
  };
}

function offsetToLocation(text, start, end) {
  const safeStart = Math.max(0, Math.min(start, text.length));
  const safeEnd = Math.max(safeStart, Math.min(end, text.length));

  let line = 1;
  let column = 1;
  let lineStart = 0;
  for (let i = 0; i < safeStart; i += 1) {
    if (text[i] === "\n") {
      line += 1;
      column = 1;
      lineStart = i + 1;
    } else {
      column += 1;
    }
  }

  let lineEnd = lineStart;
  while (lineEnd < text.length && text[lineEnd] !== "\n") {
    lineEnd += 1;
  }

  return {
    line,
    column,
    lineText: text.slice(lineStart, lineEnd),
    spanWidth: Math.max(1, safeEnd - safeStart),
  };
}

function jumpToProofDiagnostic() {
  if (!lastDiagnostic?.span) {
    return;
  }
  setActivePane("proof");
  ui.proof.focus();
  ui.proof.setSelectionRange(
    lastDiagnostic.span.start,
    Math.max(lastDiagnostic.span.start + 1, lastDiagnostic.span.end),
  );
  updateInlineDiagnosticPosition();
}

function formatApproxMs(value) {
  if (!Number.isFinite(value)) {
    return "";
  }
  if (value < 1) {
    return `≈ ${value.toFixed(1)} ms`;
  }
  if (value < 10) {
    return `≈ ${value.toFixed(1)} ms`;
  }
  return `≈ ${Math.round(value)} ms`;
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
  clearInlineDiagnostic();
}
