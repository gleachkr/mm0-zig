const encoder = new TextEncoder();
const decoder = new TextDecoder();

export const defaultWasmUrl = new URL("./lsp.wasm", import.meta.url);

export class LspServer {
  constructor(instance) {
    this.instance = instance;
    this.exports = instance.exports;
    this.subscribers = new Set();
  }

  subscribe(handler) {
    this.subscribers.add(handler);
  }

  unsubscribe(handler) {
    this.subscribers.delete(handler);
  }

  send(message) {
    const messages = this.process(message);
    for (const output of messages) {
      this.emit(output);
    }
    return messages;
  }

  process(message) {
    const inputText = typeof message === "string"
      ? message
      : JSON.stringify(message);
    const input = writeBytes(this.exports, encoder.encode(inputText));

    try {
      const ok = this.exports.process_lsp_message(input.ptr, input.len);
      const output = readLspResult(this.exports);
      if (!ok && output.length === 0) {
        throw new Error("LSP message failed");
      }
      return output.split("\n").filter((line) => line.length !== 0);
    } finally {
      freeBytes(this.exports, input);
    }
  }

  reset() {
    this.exports.reset_lsp_server();
  }

  emit(message) {
    for (const handler of this.subscribers) {
      handler(message);
    }
  }
}

export async function loadLspServer(options = {}) {
  const instance = await instantiateWasm(options, defaultWasmUrl);
  return new LspServer(instance);
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

function readLspResult(exports) {
  const ptr = exports.result_lsp_ptr();
  const len = exports.result_lsp_len();
  if (!ptr || !len) return "";
  const bytes = new Uint8Array(exports.memory.buffer, ptr, len);
  return decoder.decode(bytes);
}
