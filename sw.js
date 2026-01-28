// sw.js — Island Drone Project
// Robust, simple cache-first shell + network fallback + cache bump

const CACHE_NAME = "islanddrone-ampel-v15"; // <- bei Updates hochzählen!

const APP_SHELL = [
  "./",
  "./index.html",
  "./app.js?v=14",
  "./manifest.webmanifest",
  "./splash.jpg",
  "./sw.js"
];

// Install: cache app shell
self.addEventListener("install", (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME).then((cache) => cache.addAll(APP_SHELL))
  );
  self.skipWaiting();
});

// Activate: clean old caches
self.addEventListener("activate", (event) => {
  event.waitUntil(
    caches.keys().then((keys) =>
      Promise.all(
        keys
          .filter((k) => k.startsWith("islanddrone-ampel-") && k !== CACHE_NAME)
          .map((k) => caches.delete(k))
      )
    )
  );
  self.clients.claim();
});

// Fetch strategy:
// - For navigation (index.html): network first, fallback cache
// - For others: cache first, fallback network
self.addEventListener("fetch", (event) => {
  const req = event.request;
  const url = new URL(req.url);

  // Only handle same-origin requests (your GitHub Pages site)
  if (url.origin !== self.location.origin) return;

  // Always try fresh index.html so updates arrive
  const isNavigation =
    req.mode === "navigate" ||
    (req.destination === "document") ||
    url.pathname.endsWith("/") ||
    url.pathname.endsWith("/index.html");

  if (isNavigation) {
    event.respondWith(
      fetch(req)
        .then((res) => {
          const copy = res.clone();
          caches.open(CACHE_NAME).then((cache) => cache.put("./index.html", copy));
          return res;
        })
        .catch(() => caches.match("./index.html"))
    );
    return;
  }

  event.respondWith(
    caches.match(req).then((cached) => {
      if (cached) return cached;
      return fetch(req).then((res) => {
        // Cache successful basic responses
        if (res && res.ok && res.type === "basic") {
          const copy = res.clone();
          caches.open(CACHE_NAME).then((cache) => cache.put(req, copy));
        }
        return res;
      });
    })
  );
});
