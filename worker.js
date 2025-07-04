importScripts('./pkg/noulith.js');

// https://jasonformat.com/javascript-sleep/
function sleep(t) {
	const AB = new Int32Array(new SharedArrayBuffer(4));
	Atomics.wait(AB, 0, 0, Math.max(1, t|0));
}

(async function(){
const { encapsulated_eval } = wasm_bindgen;
await wasm_bindgen('./pkg/noulith_bg.wasm');
postMessage("ready");
addEventListener('message', async function(e) {
  let r = encapsulated_eval(e.data[0], e.data[1], e.data[2], postMessage, (e) => postMessage({ "display": e }));
  postMessage({ "error": r });
});
})();
