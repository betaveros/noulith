declare namespace wasm_bindgen {
	/* tslint:disable */
	/* eslint-disable */
	/**
	* @param {string} code
	* @param {Uint8Array} input
	* @returns {WasmOutputs}
	*/
	export function encapsulated_eval(code: string, input: Uint8Array): WasmOutputs;
	/**
	*/
	export class WasmOutputs {
	  free(): void;
	/**
	* @returns {string}
	*/
	  get_output(): string;
	/**
	* @returns {string}
	*/
	  get_error(): string;
	}
	
}

declare type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

declare interface InitOutput {
  readonly memory: WebAssembly.Memory;
  readonly __wbg_wasmoutputs_free: (a: number) => void;
  readonly wasmoutputs_get_output: (a: number, b: number) => void;
  readonly wasmoutputs_get_error: (a: number, b: number) => void;
  readonly encapsulated_eval: (a: number, b: number, c: number, d: number) => number;
  readonly __wbindgen_add_to_stack_pointer: (a: number) => number;
  readonly __wbindgen_free: (a: number, b: number) => void;
  readonly __wbindgen_malloc: (a: number) => number;
  readonly __wbindgen_realloc: (a: number, b: number, c: number) => number;
  readonly __wbindgen_exn_store: (a: number) => void;
}

/**
* If `module_or_path` is {RequestInfo} or {URL}, makes a request and
* for everything else, calls `WebAssembly.instantiate` directly.
*
* @param {InitInput | Promise<InitInput>} module_or_path
*
* @returns {Promise<InitOutput>}
*/
declare function wasm_bindgen (module_or_path?: InitInput | Promise<InitInput>): Promise<InitOutput>;
