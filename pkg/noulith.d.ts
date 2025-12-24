declare namespace wasm_bindgen {
    /* tslint:disable */
    /* eslint-disable */

    export function encapsulated_eval(code: string, input: Uint8Array, fancy: boolean, stateful: boolean, js_write: Function, js_display: Function): any;

}
declare type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

declare interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly encapsulated_eval: (a: number, b: number, c: number, d: number, e: number, f: number, g: any, h: any) => any;
    readonly __wbindgen_malloc: (a: number, b: number) => number;
    readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_exn_store: (a: number) => void;
    readonly __externref_table_alloc: () => number;
    readonly __wbindgen_externrefs: WebAssembly.Table;
    readonly __wbindgen_start: () => void;
}

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
declare function wasm_bindgen (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
