const CACHE_NAME = 'noulith-v1-0-1';
const urlsToCache = [
  './',
  './index.html',
  './readme.html',
  './builtins.html',
  './worker.js',
  './pkg/noulith.js',
  './pkg/noulith_bg.wasm',
  './ansi_up/ansi_up.js',
  './ukacd.gz',
  './yawl.gz',
  './ranked-wiki-wikt-90.gz'
];

self.addEventListener('install', event => {
  event.waitUntil(
    caches.open(CACHE_NAME)
      .then(cache => cache.addAll(urlsToCache))
  );
});

self.addEventListener('fetch', event => {
  event.respondWith(caches.match(event.request));
});

self.addEventListener('activate', event => {
  event.waitUntil(
    (async () => {
      const cacheNames = await caches.keys();
      await Promise.all(
        cacheNames.map(cacheName => {
          if (cacheName !== CACHE_NAME) {
            return caches.delete(cacheName);
          }
        })
      );
    })()
  );
});
