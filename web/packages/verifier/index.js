const encoder = new TextEncoder();
const decoder = new TextDecoder();

export const defaultWasmUrl = new URL("./verifier.wasm", import.meta.url);

export class Verifier {
  constructor(instance) {
    this.instance = instance;
    this.exports = instance.exports;
  }

  verifyPair(mm0Text, mmbBytes) {
    const mm0Bytes = encoder.encode(mm0Text);
    const mmbByteArray = byteArray(mmbBytes);
    const mm0Input = writeBytes(this.exports, mm0Bytes);
    const mmbInput = writeBytes(this.exports, mmbByteArray);

    try {
      const started = now();
      this.exports.verify_pair(
        mm0Input.ptr,
        mm0Input.len,
        mmbInput.ptr,
        mmbInput.len,
      );
      const durationMs = now() - started;
      const meta = readJsonResult(this.exports);
      return Object.assign({ meta, durationMs }, meta ?? {});
    } finally {
      freeBytes(this.exports, mm0Input);
      freeBytes(this.exports, mmbInput);
    }
  }
}

export async function loadVerifier(options = {}) {
  const instance = await instantiateWasm(options, defaultWasmUrl);
  return new Verifier(instance);
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

function byteArray(bytes) {
  if (bytes instanceof Uint8Array) return bytes;
  if (bytes instanceof ArrayBuffer) return new Uint8Array(bytes);
  if (ArrayBuffer.isView(bytes)) {
    return new Uint8Array(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  }
  throw new TypeError("mmbBytes must be a Uint8Array or ArrayBuffer");
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
