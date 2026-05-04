const encoder = new TextEncoder();
const decoder = new TextDecoder();

export const defaultWasmUrl = new URL("./compiler.wasm", import.meta.url);

export class Compiler {
  constructor(instance) {
    this.instance = instance;
    this.exports = instance.exports;
  }

  compile(mm0Text, proofText) {
    const mm0Bytes = encoder.encode(mm0Text);
    const proofBytes = encoder.encode(proofText);
    const mm0Input = writeBytes(this.exports, mm0Bytes);
    const proofInput = writeBytes(this.exports, proofBytes);

    try {
      const started = now();
      this.exports.compile_sources(
        mm0Input.ptr,
        mm0Input.len,
        proofInput.ptr,
        proofInput.len,
      );
      const durationMs = now() - started;
      const meta = readJsonResult(this.exports);
      const mmbBytes = meta?.ok
        ? readBytes(
            this.exports,
            this.exports.result_mmb_ptr(),
            this.exports.result_mmb_len(),
          )
        : new Uint8Array();
      return Object.assign({ meta, durationMs, mmbBytes }, meta ?? {});
    } finally {
      freeBytes(this.exports, mm0Input);
      freeBytes(this.exports, proofInput);
    }
  }
}

export async function loadCompiler(options = {}) {
  const instance = await instantiateWasm(options, defaultWasmUrl);
  return new Compiler(instance);
}

async function instantiateWasm(options, fallbackUrl) {
  if (options.instance) return options.instance;

  const imports = options.imports ?? {};
  if (options.module) {
    const instance = await WebAssembly.instantiate(options.module, imports);
    return instance;
  }
  if (options.wasmBytes) {
    const result = await WebAssembly.instantiate(options.wasmBytes, imports);
    return result.instance;
  }

  const url = options.wasmUrl ?? fallbackUrl;
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to load ${url}`);
  }
  const bytes = await response.arrayBuffer();
  const result = await WebAssembly.instantiate(bytes, imports);
  return result.instance;
}

function writeBytes(exports, bytes) {
  const len = bytes.length;
  const ptr = exports.alloc(len);
  if (len !== 0 && ptr === 0) {
    throw new Error("WebAssembly allocation failed");
  }
  if (len !== 0) {
    new Uint8Array(exports.memory.buffer, ptr, len).set(bytes);
  }
  return { ptr, len };
}

function freeBytes(exports, { ptr, len }) {
  exports.free(ptr, len);
}

function readBytes(exports, ptr, len) {
  if (!ptr || !len) return new Uint8Array();
  const view = new Uint8Array(exports.memory.buffer, ptr, len);
  return view.slice();
}

function readJsonResult(exports) {
  const ptr = exports.result_json_ptr();
  const len = exports.result_json_len();
  if (!ptr || !len) return null;
  const jsonBytes = new Uint8Array(exports.memory.buffer, ptr, len);
  return JSON.parse(decoder.decode(jsonBytes));
}

function now() {
  return globalThis.performance?.now?.() ?? Date.now();
}
