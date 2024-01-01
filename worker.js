importScripts('./pkg/noulith.js');

(async function(){
const { encapsulated_eval } = wasm_bindgen;
await wasm_bindgen('./pkg/noulith_bg.wasm');
postMessage("ready");
addEventListener('message', async function(e) {
  console.log('Message received from main script');
  let r = encapsulated_eval(e.data[0], e.data[1], e.data[2]);
  console.log('Posting');
  postMessage(r);
});
})();
