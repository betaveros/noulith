importScripts('./pkg/noulith.js');

(async function(){
const { encapsulated_eval } = wasm_bindgen;
await wasm_bindgen('./pkg/noulith_bg.wasm');
postMessage("ready");

addEventListener('message', async function(e) {
  let pdata = e.data[4];

  function display(e, pkey) {
    let data = { "display": e };
    if (pkey !== undefined) {
      data.persist = pkey;
    }
    if (e === false) { // special value for cache hit
      console.log("cache hit");
    } else {
      console.log("cache miss");
      postMessage(data);
    }
    return pkey === undefined ? undefined : pdata[pkey];
  };

  let r = encapsulated_eval(
    e.data[0],
    e.data[1],
    e.data[2],
    e.data[3],
    postMessage,
    display,
  );
  postMessage({ "error": r });
});
})();
