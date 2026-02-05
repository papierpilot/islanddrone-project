// sw.js — Island Drone Project
// Robust, simple cache-first shell + network fallback + cache bump
// Patch: best-effort precache + request-based navigation caching

const CACHE_NAME = "islanddrone-ampel-v28"; // <- neue Version (bei Deploy hochzählen)

const APP_SHELL = [
  "./",
  "./index.html",
  "./app.js",              // <-- wichtig: ohne ?v=
  "./manifest.webmanifest",
  "./splash.jpg",
  "./sw.js"
];

// Install: cache app shell (best effort; do NOT fail whole install if one file is missing temporarily)
self.addEventListener("install", (event) => {
  event.waitUntil((async () => {
    const cache = await caches.open(CACHE_NAME);

    await Promise.all(
      APP_SHELL.map(async (path) => {
        try {
          const res = await fetch(path, { cache: "no-cache" });
          if (res && res.ok) {
            await cache.put(path, res);
          }
        } catch (_) {
          // bewusst still: der SW soll trotzdem installieren
        }
      })
    );
  })());

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
          // Cache exactly the requested navigation URL (more robust than "./index.html" only)
          caches.open(CACHE_NAME).then((cache) => cache.put(req, copy));
          return res;
        })
        .catch(() =>
          // Try the exact request first, fallback to cached index.html
          caches.match(req).then((r) => r || caches.match("./index.html"))
        )
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
