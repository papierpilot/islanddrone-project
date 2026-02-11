// =============================
// Drone-Ampel-App – stabile Version (Island)
// + Leaflet-Karte + Pin + 500m-Kreis
// + Aviation / Schutzgebiete via WMS GetFeatureInfo
// + Overlays (WMS GetMap) schaltbar + Opacity
// + Semantik:
//    ROT  = Aviation-HIT (regelrelevant) ODER Flughafen-Policy (5km) [Standardmodus]
//    GELB = Schutzgebiet oder Grenznähe
//    INFO = Aviation-Kontext (Hinweis, kein Feature-Hit)
//    GRÜN = nichts
// + Expertenmodus: ignoriert Flughafen-Policy und zeigt rein datengestützt
// =============================

// --- 1) Aviation / Drohnenkarte (Samgöngustofa) ---
const WMS_BASE = "https://gis.natt.is/geoserver/samgongustofa/ows";
const LAYER = "samgongustofa:dronemap_ice_json";

// --- 2) Schutzgebiete (UST) ---
const PROTECTED_WMS_BASE = "https://gis.ust.is/geoserver/ows";
const PROTECTED_LAYER = "fridlyst_svaedi:fridlyst_svaedi";

// Optional Proxy (falls CORS später nervt)
const PROXY = "";

// Map defaults
const MAP_DEFAULT_ZOOM = 10;



// =============================
// Layout: make map as large as possible (esp. on mobile)
// =============================
function applyResponsiveLayout() {
  try {
    const mapEl = document.getElementById("map");
    if (!mapEl) return;

    // If there is a top info area, subtract its height only when it is part of normal flow.
    let topH = 0;
    const topEl = document.getElementById("detail");
    if (topEl) {
      const pos = window.getComputedStyle(topEl).position;
      if (pos !== "absolute" && pos !== "fixed" && pos !== "sticky") {
        topH = topEl.getBoundingClientRect().height || 0;
      }
    }

    const vh = window.innerHeight || 800;
    const h = Math.max(320, Math.floor(vh - topH - 8));

    mapEl.style.height = h + "px";
    mapEl.style.minHeight = "320px";

    // If map already exists, tell Leaflet to recalc size.
    if (typeof map !== "undefined" && map && typeof map.invalidateSize === "function") {
      map.invalidateSize();
    }
  } catch (_) {}
}

window.addEventListener("resize", () => {
  applyResponsiveLayout();
});

// =============================
// Iceland-only guard (Hard-Limit + Mask)
// =============================
const ICELAND_MIN_LAT = 63.0;
const ICELAND_MAX_LAT = 67.6;
const ICELAND_MIN_LON = -25.5;
const ICELAND_MAX_LON = -12.0;

const ENFORCE_ICELAND_ONLY = true;   // Karte/Pin/Checks nur innerhalb Island
const SHOW_OUTSIDE_WARNING = true;   // Hinweis anzeigen (gedrosselt)

let lastInsideCoords = { lat: 64.9, lon: -18.6 };
let lastOutsideWarnAt = 0;


// Grenz-Nähe (Radar)
const NEAR_DISTANCE_M = 500;
const RADAR_POINTS = 8;

// UI/Requests
const PIN_DRAG_DECIMALS = 4;
const PIN_DRAG_ACCURACY_LABEL = "manuell";

// Cache
const CACHE_TTL_MS = 30_000;
const CACHE_ROUND_DECIMALS = 5;

// GetFeatureInfo Projektion (Leaflet arbeitet in WebMercator)
const GFI_CRS = "EPSG:3857";
const GFI_HALFBOX_M = 150; // 150m in jede Richtung (Box 300m)

// =============================
// Flughafen-Schutzlogik (Policy)
// =============================
const AIRPORT_POLICY_RADIUS_M = 5000; // 5km, wie gewünscht

// Kurze Liste relevanter Flughäfen für Island.
// (Diese Liste ist bewusst klein und pragmatisch. Du kannst sie jederzeit erweitern.)
const AIRPORTS = [
  { code: "KEF", name: "Keflavík (KEF)", lat: 63.9850, lon: -22.6056 },
  { code: "RKV", name: "Reykjavík (RKV)", lat: 64.1300, lon: -21.9400 },
  { code: "AEY", name: "Akureyri (AEY)", lat: 65.6600, lon: -18.0727 },
  { code: "EGS", name: "Egilsstaðir (EGS)", lat: 65.2833, lon: -14.4014 },
  { code: "IFJ", name: "Ísafjörður (IFJ)", lat: 66.0581, lon: -23.1353 },
  { code: "VEY", name: "Vestmannaeyjar (VEY)", lat: 63.4243, lon: -20.2792 },
];

// =============================
// DOM helpers
// =============================
const el = (id) => document.getElementById(id);

// UI elements
const stateEl  = el("state");
const detailEl = el("detail");
const modeEl   = el("mode");
const coordsEl = el("coords");
const accEl    = el("acc");
const zoneEl   = el("zone");
const overlayPillEl = el("overlayPill");
const expertPillEl  = el("expertPill");

const latInput = el("lat");
const lonInput = el("lon");

// Buttons
const btnManual = el("btnManual");
const btnGps    = el("btnGps");
const btnNow    = el("btn");

// Overlay UI
const btnOverlayAvi  = el("btnOverlayAvi");
const btnOverlayProt = el("btnOverlayProt");
const overlayOpacity = el("overlayOpacity");

// Expert mode toggle
const expertToggle = el("expertToggle");

// =============================
// App State
// =============================
let currentMode = "gps"; // "gps" oder "manual"
let manualCoords = null;
let expertMode = false;

// Spot-Name (für Anfängerfreundlichkeit)
let _selectedSpotName = "";
function _setSelectedSpotName(name) { _selectedSpotName = (name || "").trim(); }
function _clearSelectedSpotName() { _selectedSpotName = ""; }

// =============================
// Leaflet state
// =============================
let map = null;
let marker = null;
let nearCircle = null;
let accuracyCircle = null;

// =============================
// WMS Overlays
// =============================
let aviationOverlay = null;
let protectedOverlay = null;
let overlayOpacityValue = 0.65;

// =============================
// Concurrency / Cancellation
// =============================
let lastRunToken = 0;
let activeController = null;

// =============================
// Cache
// =============================
const wmsCache = new Map(); // key -> {ts, value}

// =============================
// UI helpers
// =============================
function setState(kind, title, detail) {
  if (!stateEl || !detailEl) return;
  stateEl.classList.remove("ok", "no", "warn", "info");
  stateEl.classList.add(kind);
  stateEl.textContent = title;
  detailEl.textContent = detail;
}

function fmt(n) {
  return (Math.round(n * 1e6) / 1e6).toFixed(6);
}

function setMode(mode) {
  currentMode = mode;
  if (modeEl) modeEl.textContent = `Modus: ${mode === "manual" ? "manuell" : "GPS"}`;
}

function setInputs(lat, lon) {
  if (latInput) latInput.value = (Math.round(lat * 10 ** PIN_DRAG_DECIMALS) / 10 ** PIN_DRAG_DECIMALS).toFixed(PIN_DRAG_DECIMALS);
  if (lonInput) lonInput.value = (Math.round(lon * 10 ** PIN_DRAG_DECIMALS) / 10 ** PIN_DRAG_DECIMALS).toFixed(PIN_DRAG_DECIMALS);
}

function updatePills(lat, lon, accuracyText = "—") {
  if (coordsEl) {
    const spot = (typeof _selectedSpotName === "string" && _selectedSpotName) ? ` — Spot: ${_selectedSpotName}` : "";
    coordsEl.textContent = `Koordinaten: ${fmt(lat)}, ${fmt(lon)}${spot}`;
  }
  if (accEl) accEl.textContent = `Genauigkeit: ${accuracyText}`;
}

function overlayIsVisible(layer) {
  return !!(map && layer && map.hasLayer(layer));
}

function updateOverlayPill() {
  if (!overlayPillEl) return;

  const parts = [];
  if (overlayIsVisible(aviationOverlay)) parts.push("Aviation");
  if (overlayIsVisible(protectedOverlay)) parts.push("Schutzgebiete");

  if (!parts.length) {
    overlayPillEl.textContent = "Overlay: aus";
  } else {
    overlayPillEl.textContent = `Overlay: ${parts.join(" + ")} (${Math.round(overlayOpacityValue * 100)}%)`;
  }
}

function updateExpertPill() {
  if (!expertPillEl) return;
  expertPillEl.textContent = expertMode ? "Expertenmodus: an" : "Expertenmodus: aus";
}

// =============================
// Map init
// =============================
function initMap() {
  if (map) return;

  const startLat = 64.9;
  const startLon = -18.6;

  map = L.map("map", {
    zoomControl: true,
    attributionControl: true,
    maxBounds: getIcelandBounds(),
    maxBoundsViscosity: 1.0,
  }).setView([startLat, startLon], MAP_DEFAULT_ZOOM);


  // Collapsible panel integration (Map)
  try{
    window.__DA_LEAFLET_MAP__ = map;
    if (window.__DA_PANEL__ && window.__DA_PANEL__.register){
      const p = document.querySelector('[data-panel-id="map"][data-panel-collapsible="1"]');
      if (p) window.__DA_PANEL__.register(p, "map", true);
    }
  }catch(_){}

  // Make map large on mobile
  applyResponsiveLayout();

  // Ensure popup taps are not swallowed by the map on iOS
  map.on("popupopen", (e) => {
    try {
      const el = e && e.popup && e.popup.getElement ? e.popup.getElement() : null;
      if (!el) return;
      if (L && L.DomEvent) {
        L.DomEvent.disableClickPropagation(el);
        L.DomEvent.disableScrollPropagation(el);
      }
    } catch (_) {}
  });

  // Zusätzlich: nach jedem Move wieder "reinziehen" (für Touch/Browser-Eigenheiten)
  try {
    const b = getIcelandBounds();
    map.on("drag", () => { try { map.panInsideBounds(b, { animate: false }); } catch (_) {} });
    map.on("moveend", () => { try { map.panInsideBounds(b, { animate: false }); } catch (_) {} });
  } catch (_) {}

// Base Tiles (Step14): robust gegen einzelne Tile-Hosts (SSL/RateLimit/Proxy)
// Idee: wir vermeiden gezielt das "c." Subdomain (kommt in der Praxis öfter als Ausreißer),
// und schalten bei mehreren Fehlern innerhalb kurzer Zeit automatisch auf Fallback um.
const __tileOpts = {
  maxZoom: 19,
  noWrap: true,
  bounds: getIcelandBounds(),
  attribution: "&copy; OpenStreetMap contributors",
  updateWhenIdle: true,
  // bewusst ohne "c" um SSL-Glitches / Blockaden zu umgehen
  subdomains: ["a","b"],
};

let __baseTileLayer = null;
const __tileFail = { count: 0, t0: 0, switched: false };

function __attachTileErrorHandler(layer){
  layer.on("tileerror", () => {
    const now = Date.now();
    if(!__tileFail.t0 || (now - __tileFail.t0) > 5000){
      __tileFail.t0 = now;
      __tileFail.count = 0;
    }
    __tileFail.count++;

    // nach 3 Fehlern/5s: Fallback schalten (einmalig)
    if(!__tileFail.switched && __tileFail.count >= 3){
      __tileFail.switched = true;
      try { map.removeLayer(layer); } catch(_){}

      // Fallback: anderer OSM Tile Host (gleiches Daten-Ökosystem)
      __baseTileLayer = L.tileLayer("https://tile.openstreetmap.de/{z}/{x}/{y}.png", {
        maxZoom: 19,
        noWrap: true,
        bounds: getIcelandBounds(),
        attribution: "&copy; OpenStreetMap contributors",
        updateWhenIdle: true,
      }).addTo(map);
    }
  });
}

__baseTileLayer = L.tileLayer("https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png", __tileOpts).addTo(map);
__attachTileErrorHandler(__baseTileLayer);


  // Welt-Maske: alles außerhalb Islands abdunkeln (nur visuell)
  try {
    const b = getIcelandBounds();
    const outer = [[-90, -180], [-90, 180], [90, 180], [90, -180], [-90, -180]];
    const sw = b.getSouthWest();
    const ne = b.getNorthEast();
    const inner = [[sw.lat, sw.lng], [sw.lat, ne.lng], [ne.lat, ne.lng], [ne.lat, sw.lng], [sw.lat, sw.lng]];

    if (!map.getPane("maskPane")) {
      map.createPane("maskPane");
      map.getPane("maskPane").style.zIndex = 350;
      map.getPane("maskPane").style.pointerEvents = "none";
    }

    L.polygon([outer, inner], {
      pane: "maskPane",
      stroke: false,
      fill: true,
      fillOpacity: 0.55,
      fillColor: "#000",
      interactive: false,
    }).addTo(map);
  } catch (_) {}

  marker = L.marker([startLat, startLon], { draggable: true }).addTo(map);

  nearCircle = L.circle([startLat, startLon], {
    radius: NEAR_DISTANCE_M,
    weight: 2,
    opacity: 0.8,
    fillOpacity: 0.06,
  }).addTo(map);

  accuracyCircle = L.circle([startLat, startLon], {
    radius: 0,
    weight: 1,
    opacity: 0.5,
    fillOpacity: 0.04,
  }).addTo(map);

  marker.on("drag", () => {
    try { _clearSelectedSpotName(); } catch (_) {}
    const p0 = marker.getLatLng();
    let lat = p0.lat;
    let lon = p0.lng;

    const g = guardToIceland(lat, lon, "Island-only: Außerhalb Islands wird blockiert. Marker bleibt innerhalb der Karte.");
    lat = g.lat;
    lon = g.lon;

    if (!g.inside) {
      try { marker.setLatLng([lat, lon]); } catch (_) {}
      try { map && map.panInsideBounds(getIcelandBounds(), { animate: false }); } catch (_) {}
    }

    setMode("manual");
    setInputs(lat, lon);
    updatePills(lat, lon, PIN_DRAG_ACCURACY_LABEL);

    const p = { lat, lng: lon };
    nearCircle.setLatLng(p);
    accuracyCircle.setLatLng(p);
  });

  marker.on("dragend", async () => {
    try { _clearSelectedSpotName(); } catch (_) {}
    const p0 = marker.getLatLng();
    let lat = p0.lat;
    let lon = p0.lng;

    const g = guardToIceland(lat, lon, "Island-only: Punkt liegt außerhalb Islands. Ich setze ihn zurück in den gültigen Bereich.");
    lat = g.lat;
    lon = g.lon;

    try { marker.setLatLng([lat, lon]); } catch (_) {}
    try { updateMap(lat, lon, PIN_DRAG_ACCURACY_LABEL); } catch (_) {}

    setMode("manual");
    manualCoords = { lat, lon };
    try {
      await runCheckWithCoords(lat, lon, PIN_DRAG_ACCURACY_LABEL, null);
    } catch (e) {
      setState("warn", "—", `Abfrage fehlgeschlagen: ${e.message}`);
    }
  });

  // Map Klick: Detail-Popup (Aviation/Schutzgebiet) + Airport-Policy Hinweis
  map.on("click", async (e) => {
    const { lat, lng } = e.latlng;
    if (ENFORCE_ICELAND_ONLY && !isInsideIceland(lat, lng)) {
      if (SHOW_OUTSIDE_WARNING) setState("info", "—", "Island-only: Klick außerhalb Islands – keine Detailabfrage.");
      return;
    }
    try {
      const res = await runDetailQuery(lat, lng);
      const ap = nearestAirport(lat, lng);

      const lines = [];
      lines.push(`<b>Detailabfrage</b>`);
      lines.push(`Koordinaten: ${fmt(lat)}, ${fmt(lng)}`);

      // Aviation
      const aviText =
        res.aviationLevel === "hit" ? "Treffer" :
        res.aviationLevel === "context" ? "Kontext" :
        "kein Treffer";

      // Protected
      const protText = res.protectedHit ? "Treffer" : "kein Treffer";

      lines.push(`Aviation: ${aviText}${res.aviName ? " – " + escapeHtml(res.aviName) : ""}`);
      lines.push(`Schutzgebiet: ${protText}${res.protName ? " – " + escapeHtml(res.protName) : ""}`);

      // Airport policy info
      if (ap && ap.distanceM != null) {
        const d = Math.round(ap.distanceM);
        const inRing = d <= AIRPORT_POLICY_RADIUS_M;
        lines.push(`Flughafen: ${escapeHtml(ap.airport.name)} (${d} m)${inRing ? " – <b>im 5km-Ring</b>" : ""}`);
      }

      lines.push(`Vertrauen: ${escapeHtml(res.confidence)}`);
      if (res.errSum) lines.push(`<span style="opacity:.85">Hinweis: ${escapeHtml(res.errSum)}</span>`);

      L.popup()
        .setLatLng(e.latlng)
        .setContent(lines.join("<br/>"))
        .openOn(map);
    } catch (err) {
      L.popup()
        .setLatLng(e.latlng)
        .setContent(`<b>Detailabfrage</b><br/>Fehler: ${escapeHtml(err.message || String(err))}`)
        .openOn(map);
    }
  });

  prepareOverlays();
  updateOverlayPill();
}

function updateMap(lat, lon, accuracyMeters = null) {
  initMap();

  const g = guardToIceland(lat, lon);
  const p = { lat: g.lat, lon: g.lon };

  try { marker.setLatLng([p.lat, p.lon]); } catch (_) {}
  try { map.setView([p.lat, p.lon], MAP_DEFAULT_ZOOM, { animate: true }); } catch (_) {}
  try { map.panInsideBounds(getIcelandBounds(), { animate: false }); } catch (_) {}

  nearCircle.setLatLng([p.lat, p.lon]);
  accuracyCircle.setLatLng([p.lat, p.lon]);
  accuracyCircle.setRadius(Number.isFinite(accuracyMeters) ? Math.max(accuracyMeters, 0) : 0);
}

// =============================
// WMS Overlays (GetMap) – VISUALISIERUNG
// =============================
function prepareOverlays() {
  if (!map) return;

  if (!aviationOverlay) {
    aviationOverlay = L.tileLayer.wms(WMS_BASE, {
      layers: LAYER,
      format: "image/png",
      transparent: true,
      version: "1.3.0",
      opacity: overlayOpacityValue,
      attribution: "Aviation WMS (Samgöngustofa)",
    });
  }

  if (!protectedOverlay) {
    protectedOverlay = L.tileLayer.wms(PROTECTED_WMS_BASE, {
      layers: PROTECTED_LAYER,
      format: "image/png",
      transparent: true,
      version: "1.3.0",
      opacity: overlayOpacityValue,
      attribution: "Protected Areas WMS (UST)",
    });
  }
}

function setOverlayOpacity(v) {
  overlayOpacityValue = Math.max(0, Math.min(1, v));
  if (aviationOverlay) aviationOverlay.setOpacity(overlayOpacityValue);
  if (protectedOverlay) protectedOverlay.setOpacity(overlayOpacityValue);
  updateOverlayPill();
}

function toggleAviationOverlay() {
  initMap();
  prepareOverlays();
  if (!aviationOverlay) return;

  if (overlayIsVisible(aviationOverlay)) map.removeLayer(aviationOverlay);
  else aviationOverlay.addTo(map);

  updateOverlayPill();
}

function toggleProtectedOverlay() {
  initMap();
  prepareOverlays();
  if (!protectedOverlay) return;

  if (overlayIsVisible(protectedOverlay)) map.removeLayer(protectedOverlay);
  else protectedOverlay.addTo(map);

  updateOverlayPill();
}

// =============================
// Geo / Airport helpers
// =============================
function toRad(x) { return x * Math.PI / 180; }

function haversineMeters(lat1, lon1, lat2, lon2) {
  const R = 6371000; // m
  const dLat = toRad(lat2 - lat1);
  const dLon = toRad(lon2 - lon1);
  const a =
    Math.sin(dLat / 2) ** 2 +
    Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLon / 2) ** 2;
  const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  return R * c;
}

function nearestAirport(lat, lon) {
  if (!AIRPORTS.length) return null;
  let best = null;
  for (const ap of AIRPORTS) {
    const d = haversineMeters(lat, lon, ap.lat, ap.lon);
    if (!best || d < best.distanceM) {
      best = { airport: ap, distanceM: d };
    }
  }
  return best;
}

// =============================
// GetFeatureInfo helpers – LOGIK
// =============================
function latLonToWebMercator(lat, lon) {
  const R = 6378137;
  const x = R * (lon * Math.PI / 180);
  const y = R * Math.log(Math.tan(Math.PI / 4 + (lat * Math.PI / 180) / 2));
  return { x, y };
}

function makeBbox3857(lat, lon, halfBoxM = GFI_HALFBOX_M) {
  const { x, y } = latLonToWebMercator(lat, lon);
  return { minX: x - halfBoxM, minY: y - halfBoxM, maxX: x + halfBoxM, maxY: y + halfBoxM };
}

function buildGfiUrl(baseUrl, layerName, bbox, infoFormat) {
  const bboxStr = `${bbox.minX},${bbox.minY},${bbox.maxX},${bbox.maxY}`;

  const params = new URLSearchParams({
    SERVICE: "WMS",
    VERSION: "1.3.0",
    REQUEST: "GetFeatureInfo",
    LAYERS: layerName,
    QUERY_LAYERS: layerName,
    INFO_FORMAT: infoFormat,
    CRS: GFI_CRS,
    BBOX: bboxStr,
    WIDTH: "101",
    HEIGHT: "101",
    I: "50",
    J: "50",
    FEATURE_COUNT: "5",
  });

  const url = `${baseUrl}?${params.toString()}`;
  return PROXY ? PROXY + encodeURIComponent(url) : url;
}

async function fetchText(url, signal) {
  const res = await fetch(url, { cache: "no-cache", signal });
  if (!res.ok) throw new Error(`HTTP ${res.status}`);
  return await res.text();
}

function isWmsException(text) {
  const x = text || "";
  return x.includes("ServiceException") || x.includes("ExceptionReport") || x.includes("ows:Exception");
}

function parseFeatureCount(xmlText) {
  try {
    const parser = new DOMParser();
    const xml = parser.parseFromString(xmlText, "text/xml");
    const pe = xml.getElementsByTagName("parsererror");
    if (pe && pe.length) return 0;
    if (isWmsException(xmlText)) return 0;

    const a = xml.getElementsByTagName("featureMember");
    const b = xml.getElementsByTagName("gml:featureMember");
    const c = xml.getElementsByTagName("featureMembers");
    const d = xml.getElementsByTagName("gml:featureMembers");

    return (a?.length || 0) + (b?.length || 0) + (c?.length || 0) + (d?.length || 0);
  } catch (_) {
    return 0;
  }
}

// Aviation "hit" = echtes Feature (regelrelevant)
// Aviation "context" = FeatureInfoResponse/FIELDS/Text (Hinweis), aber kein FeatureMember
function aviationLevelFromXml(xmlText) {
  if (!xmlText || isWmsException(xmlText)) return "none";

  const count = parseFeatureCount(xmlText);
  if (count > 0) return "hit";

  const t = xmlText.toLowerCase();
  if (t.includes("featureinforesponse")) return "context";
  if (t.includes("<fields")) return "context";

  return "none";
}

function aviationLevelFromText(text) {
  const t = (text || "").trim();
  if (!t) return "none";
  const low = t.toLowerCase();
  if (low.includes("serviceexception") || low.includes("exceptionreport")) return "none";
  return "context";
}

function tryExtractZoneNameFromXml(xmlText) {
  try {
    const parser = new DOMParser();
    const xml = parser.parseFromString(xmlText, "text/xml");
    const candidates = ["name", "NAME", "title", "TITLE", "zone", "ZONE", "designation", "DESIGNATION", "id", "ID"];
    for (const tag of candidates) {
      const n = xml.getElementsByTagName(tag);
      if (n && n.length > 0) {
        const val = (n[0].textContent || "").trim();
        if (val) return val;
      }
    }
  } catch (_) {}
  return null;
}

// =============================
// Cache helpers
// =============================
function roundDec(x, d) {
  const p = 10 ** d;
  return Math.round(x * p) / p;
}

function makeCacheKey(baseUrl, layerName, lat, lon) {
  const rLat = roundDec(lat, CACHE_ROUND_DECIMALS);
  const rLon = roundDec(lon, CACHE_ROUND_DECIMALS);
  return `${baseUrl}|${layerName}|${rLat},${rLon}|${GFI_CRS}|${GFI_HALFBOX_M}`;
}

function cacheGet(key) {
  const it = wmsCache.get(key);
  if (!it) return null;
  if ((Date.now() - it.ts) > CACHE_TTL_MS) {
    wmsCache.delete(key);
    return null;
  }
  return it.value;
}

function cacheSet(key, value) {
  wmsCache.set(key, { ts: Date.now(), value });
}

// =============================
// Query WMS (GetFeatureInfo)
// - Aviation => level: hit/context/none
// - Schutzgebiete => hit: true/false
// =============================
async function queryAviation(baseUrl, layerName, lat, lon, signal) {
  const cacheKey = makeCacheKey(baseUrl, layerName, lat, lon) + "|avi";
  const cached = cacheGet(cacheKey);
  if (cached) return { ...cached, cached: true };

  const bbox = makeBbox3857(lat, lon, GFI_HALFBOX_M);

  // 1) JSON
  try {
    const res = await fetch(buildGfiUrl(baseUrl, layerName, bbox, "application/json"), { cache: "no-cache", signal });
    if (res.ok) {
      const js = await res.json();
      const hit = Array.isArray(js?.features) ? js.features.length > 0 : false;
      const out = { level: hit ? "hit" : "none", raw: js, format: "json", cached: false };
      cacheSet(cacheKey, out);
      return out;
    }
  } catch (_) {}

  // 2) XML
  try {
    const xml = await fetchText(buildGfiUrl(baseUrl, layerName, bbox, "text/xml"), signal);
    const level = aviationLevelFromXml(xml);
    const out = { level, raw: xml, format: "xml", cached: false };
    cacheSet(cacheKey, out);
    return out;
  } catch (_) {}

  // 3) text/plain
  const txt = await fetchText(buildGfiUrl(baseUrl, layerName, bbox, "text/plain"), signal);
  const level = aviationLevelFromText(txt);
  const out = { level, raw: txt, format: "text", cached: false };
  cacheSet(cacheKey, out);
  return out;
}

async function queryProtected(baseUrl, layerName, lat, lon, signal) {
  const cacheKey = makeCacheKey(baseUrl, layerName, lat, lon) + "|prot";
  const cached = cacheGet(cacheKey);
  if (cached) return { ...cached, cached: true };

  const bbox = makeBbox3857(lat, lon, GFI_HALFBOX_M);

  // 1) JSON
  try {
    const res = await fetch(buildGfiUrl(baseUrl, layerName, bbox, "application/json"), { cache: "no-cache", signal });
    if (res.ok) {
      const js = await res.json();
      const hit = Array.isArray(js?.features) ? js.features.length > 0 : false;
      const out = { hit, raw: js, format: "json", cached: false };
      cacheSet(cacheKey, out);
      return out;
    }
  } catch (_) {}

  // 2) XML
  const xml = await fetchText(buildGfiUrl(baseUrl, layerName, bbox, "text/xml"), signal);
  const hit = parseFeatureCount(xml) > 0;
  const out = { hit, raw: xml, format: "xml", cached: false };
  cacheSet(cacheKey, out);
  return out;
}

// =============================
// Near-Check (Radar)
// =============================
function offsetMeters(lat, lon, eastMeters, northMeters) {
  const dLat = northMeters / 111320;
  const dLon = eastMeters / (111320 * Math.cos((lat * Math.PI) / 180));
  return { lat: lat + dLat, lon: lon + dLon };
}

function makeRadarPoints(lat, lon, radiusM, n) {
  const pts = [];
  for (let i = 0; i < n; i++) {
    const a = (2 * Math.PI * i) / n;
    const east = Math.cos(a) * radiusM;
    const north = Math.sin(a) * radiusM;
    pts.push(offsetMeters(lat, lon, east, north));
  }
  return pts;
}

// =============================
// Layer Checks
// =============================
async function checkBothLayers(lat, lon, signal) {
  const [avi, prot] = await Promise.allSettled([
    queryAviation(WMS_BASE, LAYER, lat, lon, signal),
    queryProtected(PROTECTED_WMS_BASE, PROTECTED_LAYER, lat, lon, signal),
  ]);

  const aviOk = avi.status === "fulfilled" ? avi.value : null;
  const protOk = prot.status === "fulfilled" ? prot.value : null;

  const aviErr = avi.status === "rejected" ? (avi.reason?.message || String(avi.reason)) : null;
  const protErr = prot.status === "rejected" ? (prot.reason?.message || String(prot.reason)) : null;

  return {
    aviationLevel: aviOk ? aviOk.level : "none",
    protectedHit: protOk ? protOk.hit : false,
    aviOk,
    protOk,
    aviErr,
    protErr,
  };
}

function summarizeErrors(aviErr, protErr) {
  const parts = [];
  if (aviErr) parts.push(`Aviation: ${aviErr}`);
  if (protErr) parts.push(`Schutzgebiete: ${protErr}`);
  return parts.join(" | ");
}

function confidenceLabel(aviErr, protErr) {
  const a = !!aviErr;
  const p = !!protErr;
  if (!a && !p) return "hoch";
  if (a && p) return "niedrig";
  return "mittel";
}

async function nearCheck(lat, lon, signal) {
  const pts = makeRadarPoints(lat, lon, NEAR_DISTANCE_M, RADAR_POINTS);
  const checks = pts.map((p) => checkBothLayers(p.lat, p.lon, signal));
  const results = await Promise.allSettled(checks);

  let nearAviationHit = false;
  let nearProtected = false;
  let hadErrors = false;

  for (const r of results) {
    if (r.status === "fulfilled") {
      const v = r.value;
      if (v.aviErr || v.protErr) hadErrors = true;
      if (v.aviationLevel === "hit") nearAviationHit = true;
      if (v.protectedHit) nearProtected = true;
    } else {
      hadErrors = true;
    }
  }

  return { nearAviationHit, nearProtected, hadErrors };
}

// =============================
// Main Check
// =============================
async function runCheckWithCoords(lat, lon, accuracyText = "—", accuracyMeters = null) {
  const myToken = ++lastRunToken;

  // Cancel previous
  if (activeController) {
    try { activeController.abort(); } catch (_) {}
  }
  activeController = new AbortController();
  const signal = activeController.signal;

  const stopIfStale = () => (myToken !== lastRunToken);

  if (zoneEl) zoneEl.textContent = "Zone: —";
  updatePills(lat, lon, accuracyText);
  setInputs(lat, lon);
  updateMap(lat, lon, accuracyMeters);
  updateExpertPill();

  // 0) Flughafen-Policy (nur im Standardmodus)
  //    => konservativ ROT, bevor wir überhaupt Daten abfragen
  const ap = nearestAirport(lat, lon);
  if (!expertMode && ap && ap.distanceM <= AIRPORT_POLICY_RADIUS_M) {
    const d = Math.round(ap.distanceM);
    if (zoneEl) zoneEl.textContent = `Zone: Flughafen-Nähe (${ap.airport.code})`;

    setState(
      "no",
      "ROT",
      `${ap.airport.name}: ${d} m. Konservativer 5km-Sicherheitsring (Policy). Bitte nicht fliegen ohne explizite Freigabe/Regelprüfung.`
    );

    // Aviation-Overlay automatisch an (damit man Kontext sieht)
    prepareOverlays();
    if (!overlayIsVisible(aviationOverlay) && aviationOverlay) aviationOverlay.addTo(map);
    updateOverlayPill();
    return;
  }

  setState("warn", "…", "Frage Server (Aviation + Schutzgebiete)…");

  try {
    const base = await checkBothLayers(lat, lon, signal);
    if (stopIfStale()) return;

    const errSum = summarizeErrors(base.aviErr, base.protErr);
    const conf = confidenceLabel(base.aviErr, base.protErr);

    // 1) ROT: Aviation HIT (regelrelevant)
    if (base.aviationLevel === "hit") {
      let name = null;
      if (base.aviOk?.format === "xml") name = tryExtractZoneNameFromXml(base.aviOk.raw);
      if (zoneEl) zoneEl.textContent = `Zone: ${name ? name : "Aviation-Zone"}`;

      setState("no", "ROT", `Treffer: Aviation/Luftraum (regelrelevant). Vertrauen: ${conf}.`);
      if (errSum) detailEl.textContent += ` | Hinweis: ${errSum}`;

      prepareOverlays();
      if (!overlayIsVisible(aviationOverlay) && aviationOverlay) aviationOverlay.addTo(map);
      updateOverlayPill();
      return;
    }

    // 2) GELB: Schutzgebiet HIT
    if (base.protectedHit) {
      let name = null;
      if (base.protOk?.format === "xml") name = tryExtractZoneNameFromXml(base.protOk.raw);
      if (zoneEl) zoneEl.textContent = `Zone: ${name ? name : "Schutzgebiet"}`;

      setState("warn", "GELB", `Schutzgebiet: sensibler Bereich. Vertrauen: ${conf}. Regeln können variieren – bitte amtlich prüfen.`);
      if (errSum) detailEl.textContent += ` | Hinweis: ${errSum}`;
      return;
    }

    // 3) INFO: Aviation KONTEXT (Hinweis, kein Feature-Hit)
    if (base.aviationLevel === "context") {
      if (zoneEl) zoneEl.textContent = "Zone: Aviation-Kontext";
      setState(
        "info",
        "INFO",
        `Aviation-Umfeld (Hinweis). Kein explizites Verbot als Feature. Vertrauen: ${conf}. Bitte besonders aufmerksam (lokale Regeln, Start-/Landeachsen, NOTAM, Menschen).`
      );
      if (errSum) detailEl.textContent += ` | Hinweis: ${errSum}`;
      return;
    }

    // 4) Kein Treffer am Punkt -> Grenznähe prüfen
    setState("warn", "…", `Kein Treffer am Punkt. Prüfe Grenznähe (${NEAR_DISTANCE_M} m)…`);
    const near = await nearCheck(lat, lon, signal);
    if (stopIfStale()) return;

    const reasons = [];
    if (near.nearAviationHit) reasons.push(`Grenzbereich Aviation (<${NEAR_DISTANCE_M} m)`);
    if (near.nearProtected) reasons.push(`nahe Schutzgebiet (<${NEAR_DISTANCE_M} m)`);
    if (errSum) reasons.push("Quellen nicht vollständig erreichbar");

    if (reasons.length) {
      setState("warn", "GELB", `Vorsicht: ${reasons.join(" | ")}. Vertrauen: ${conf}.`);
      if (near.hadErrors) detailEl.textContent += " | Hinweis: Grenz-Check evtl. unvollständig.";
      return;
    }

    // 5) GRÜN (nur wenn nicht total blind)
    if (conf === "niedrig") {
      setState("warn", "GELB", "Keine Treffer – aber Quellen waren nicht erreichbar. Bitte später erneut prüfen. Vertrauen: niedrig.");
      return;
    }

    // Optional: im Expertenmodus trotzdem Flughafen-Hinweistext als Info in Detail (nicht als Ampel)
    if (expertMode && ap && ap.distanceM <= AIRPORT_POLICY_RADIUS_M) {
      setState("info", "INFO", `Expertenmodus: im 5km-Ring von ${ap.airport.name} (${Math.round(ap.distanceM)} m) – Ampel bleibt datengestützt.`);
      return;
    }

    setState("ok", "GRÜN", `Keine Zone laut Servern. Vertrauen: ${conf}. (Aviation + Schutzgebiete)`);
  } catch (e) {
    if (e?.name === "AbortError") return;
    setState("warn", "—", `Abfrage fehlgeschlagen: ${e.message}`);
  }
}

// =============================
// Detail Query (Map-Klick Popup)
// =============================
async function runDetailQuery(lat, lon) {
  const controller = new AbortController();
  const signal = controller.signal;

  const base = await checkBothLayers(lat, lon, signal);

  const errSum = summarizeErrors(base.aviErr, base.protErr);
  const conf = confidenceLabel(base.aviErr, base.protErr);

  let aviName = null;
  if (base.aviOk?.format === "xml" && base.aviationLevel === "hit") {
    aviName = tryExtractZoneNameFromXml(base.aviOk.raw);
  }

  let protName = null;
  if (base.protOk?.format === "xml" && base.protectedHit) {
    protName = tryExtractZoneNameFromXml(base.protOk.raw);
  }

  return {
    aviationLevel: base.aviationLevel,
    protectedHit: base.protectedHit,
    aviName,
    protName,
    confidence: conf,
    errSum,
  };
}

// =============================
// GPS / Manual
// =============================
async function checkGps() {
  try { _clearSelectedSpotName(); } catch (_) {}
  if (!navigator.geolocation) {
    setState("warn", "—", "GPS nicht verfügbar.");
    return;
  }

  setMode("gps");
  setState("warn", "…", "Standort wird geholt…");

  navigator.geolocation.getCurrentPosition(
    async (pos) => {
      const { latitude, longitude, accuracy } = pos.coords;
      const accText = accuracy ? `±${Math.round(accuracy)} m` : "—";
      const g = guardToIceland(latitude, longitude, "Island-only: GPS liegt außerhalb Islands – ich klemme den Punkt zurück.");
    updateMap(g.lat, g.lon, accuracy);
    await runCheckWithCoords(g.lat, g.lon, accText, accuracy);
    },
    (err) => setState("warn", "—", `Standortfehler: ${err.message}`),
    { enableHighAccuracy: true, timeout: 12000, maximumAge: 2000 }
  );
}

function parseManualInputs() {
  const lat = Number(String(latInput?.value ?? "").replace(",", "."));
  const lon = Number(String(lonInput?.value ?? "").replace(",", "."));

  if (!Number.isFinite(lat) || !Number.isFinite(lon)) {
    throw new Error("Bitte gültige Latitude/Longitude eingeben (Zahlen).");
  }
  if (lat < -90 || lat > 90) throw new Error("Latitude muss zwischen -90 und 90 liegen.");
  if (lon < -180 || lon > 180) throw new Error("Longitude muss zwischen -180 und 180 liegen.");
  return { lat, lon };
}

async function checkManual() {
  try { _clearSelectedSpotName(); } catch (_) {}
  setMode("manual");
  try {
    manualCoords = parseManualInputs();
    const g = guardToIceland(manualCoords.lat, manualCoords.lon, "Island-only: Manuelle Koordinaten außerhalb Islands – ich klemme sie zurück.");
    manualCoords = { lat: g.lat, lon: g.lon };
    setInputs(g.lat, g.lon);
    updateMap(g.lat, g.lon, "manuell");
    await runCheckWithCoords(g.lat, g.lon, "manuell", null);
  } catch (e) {
    setState("warn", "—", e.message);
  }
}

async function checkCurrentMode() {
  if (currentMode === "manual") return checkManual();
  return checkGps();
}

// =============================

function getIcelandBounds() {
  return L.latLngBounds(
    [ICELAND_MIN_LAT, ICELAND_MIN_LON],
    [ICELAND_MAX_LAT, ICELAND_MAX_LON]
  );
}

function isInsideIceland(lat, lon) {
  try {
    return getIcelandBounds().contains([lat, lon]);
  } catch (_) {
    return (
      lat >= ICELAND_MIN_LAT && lat <= ICELAND_MAX_LAT &&
      lon >= ICELAND_MIN_LON && lon <= ICELAND_MAX_LON
    );
  }
}

function clampToIceland(lat, lon) {
  const clampedLat = Math.min(ICELAND_MAX_LAT, Math.max(ICELAND_MIN_LAT, lat));
  const clampedLon = Math.min(ICELAND_MAX_LON, Math.max(ICELAND_MIN_LON, lon));
  return { lat: clampedLat, lon: clampedLon };
}

function guardToIceland(lat, lon, message) {
  if (!ENFORCE_ICELAND_ONLY) return { lat, lon, inside: true };

  if (isInsideIceland(lat, lon)) {
    lastInsideCoords = { lat, lon };
    return { lat, lon, inside: true };
  }

  const c = clampToIceland(lat, lon);

  const now = Date.now();
  if (SHOW_OUTSIDE_WARNING && (now - lastOutsideWarnAt > 1200)) {
    lastOutsideWarnAt = now;
    setState("info", "—", message || "Island-only: Punkt außerhalb Islands – ich klemme ihn zurück in den gültigen Bereich.");
  }

  return { lat: c.lat, lon: c.lon, inside: false };
}


// Utils
// =============================
function escapeHtml(s) {
  return String(s)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

// =============================
// Maps handoff (optional)
// - Opens a coordinate in the user's maps app (usually Google Maps; falls back to browser)
// - No routing, no navigation logic inside this app
// =============================
function openInMaps(lat, lon, name = "") {
  const n = Number(lat);
  const e = Number(lon);
  if (!Number.isFinite(n) || !Number.isFinite(e)) return;

  const label = String(name || "").trim();
  // Universal: works on iOS + Android, opens installed app when available
  const url = `https://www.google.com/maps/search/?api=1&query=${encodeURIComponent(`${n},${e}${label ? ` (${label})` : ""}`)}`;
  try {
    window.open(url, "_blank", "noopener,noreferrer");
  } catch (_) {
    window.location.href = url;
  }
}

// iOS/Leaflet: Popups sometimes swallow taps. We route the "In Maps öffnen" action
// through a delegated handler (capture phase) so it works reliably on iPhone + Android.
let _mapsBtnLastTs = 0;
function _mapsBtnHandle(ev) {
  try {
    const t = Date.now();
    if (t - _mapsBtnLastTs < 700) return; // guard double-trigger (touch + click)
    const target = ev && ev.target;
    if (!target || !target.closest) return;
    const btn = target.closest(".maps-btn");
    if (!btn) return;

    _mapsBtnLastTs = t;

    if (ev.preventDefault) ev.preventDefault();
    if (ev.stopPropagation) ev.stopPropagation();
    if (ev.stopImmediatePropagation) ev.stopImmediatePropagation();

    const lat = btn.getAttribute("data-lat");
    const lon = btn.getAttribute("data-lon");
    const rawName = btn.getAttribute("data-name") || "";
    let name = rawName;
    try { name = JSON.parse(rawName); } catch (_) {}

    openInMaps(lat, lon, name);
  } catch (_) {}
}

document.addEventListener("click", _mapsBtnHandle, true);
document.addEventListener("touchend", _mapsBtnHandle, { capture: true, passive: false });

// =============================
// Copy-to-Clipboard (Spot Koordinaten)
// - bewusst neutral: nur Koordinaten, keine Navigation
// - iOS-safe: delegated handler + clipboard fallback
// =============================
function _copyTextToClipboard(text) {
  const t = String(text || "").trim();
  if (!t) return Promise.reject(new Error("empty"));

  // Modern API
  try {
    if (navigator && navigator.clipboard && typeof navigator.clipboard.writeText === "function") {
      return navigator.clipboard.writeText(t);
    }
  } catch (_) {}

  // Fallback (iOS/older browsers)
  return new Promise((resolve, reject) => {
    try {
      const ta = document.createElement("textarea");
      ta.value = t;
      ta.setAttribute("readonly", "");
      ta.style.position = "fixed";
      ta.style.top = "-1000px";
      ta.style.left = "-1000px";
      ta.style.opacity = "0";
      document.body.appendChild(ta);
      ta.select();
      ta.setSelectionRange(0, ta.value.length);
      const ok = document.execCommand("copy");
      document.body.removeChild(ta);
      ok ? resolve() : reject(new Error("execCommand failed"));
    } catch (e) {
      reject(e);
    }
  });
}

let _copyBtnLastTs = 0;
function _copyBtnHandle(ev) {
  try {
    const t = Date.now();
    if (t - _copyBtnLastTs < 700) return; // guard double-trigger (touch + click)
    const target = ev && ev.target;
    if (!target || !target.closest) return;
    const btn = target.closest(".copy-btn");
    if (!btn) return;

    _copyBtnLastTs = t;

    if (ev.preventDefault) ev.preventDefault();
    if (ev.stopPropagation) ev.stopPropagation();
    if (ev.stopImmediatePropagation) ev.stopImmediatePropagation();

    const coords = btn.getAttribute("data-coords") || "";
    const before = btn.textContent;
    _copyTextToClipboard(coords).then(() => {
      try {
        btn.textContent = "Kopiert ✓";
        setTimeout(() => { try { btn.textContent = before; } catch (_) {} }, 1200);
      } catch (_) {}
    }).catch(() => {
      // leise bleiben – kein Popup-Spam
      try {
        btn.textContent = "Nicht kopiert";
        setTimeout(() => { try { btn.textContent = before; } catch (_) {} }, 1200);
      } catch (_) {}
    });
  } catch (_) {}
}

document.addEventListener("click", _copyBtnHandle, true);
document.addEventListener("touchend", _copyBtnHandle, { capture: true, passive: false });




// openInMaps is used by the popup button handler onclick
try { window.openInMaps = openInMaps; } catch (_) {}


// =============================
// Wire buttons (safe)
// =============================
if (btnManual) btnManual.addEventListener("click", checkManual);
if (btnGps)    btnGps.addEventListener("click", checkGps);
if (btnNow)    btnNow.addEventListener("click", checkCurrentMode);

if (btnOverlayAvi)  btnOverlayAvi.addEventListener("click", toggleAviationOverlay);
if (btnOverlayProt) btnOverlayProt.addEventListener("click", toggleProtectedOverlay);

if (overlayOpacity) {
  const v = Number(overlayOpacity.value);
  if (Number.isFinite(v)) overlayOpacityValue = Math.max(0, Math.min(1, v));
  overlayOpacity.addEventListener("input", (e) => {
    const nv = Number(e.target.value);
    if (Number.isFinite(nv)) setOverlayOpacity(nv);
  });
}

if (expertToggle) {
  expertMode = !!expertToggle.checked;
  expertToggle.addEventListener("change", () => {
    expertMode = !!expertToggle.checked;
    updateExpertPill();
  });
}

// =============================
// Start
// =============================
initMap();
setMode("gps");
updateExpertPill();
updateOverlayPill();
setState("warn", "—", "Bereit. Nutze GPS oder gib Koordinaten ein.");


// =============================
// WINDMODUL – Open-Meteo (frei) + DJI-Referenz (konservativ)
// - Wind/Böen/Richtung live
// - Update bei jeder Pin-Bewegung (gedrosselt)
// =============================

const WIND_API_BASE = "https://api.open-meteo.com/v1/forecast";
const WIND_THROTTLE_MS = 12_000;

// DJI Klassen (konservativ, m/s)
const WIND_DJI_CLASSES = [
  { key: "mini",  label: "DJI Mini",        greenMax: 6,  yellowMax: 8,  gustRed: 9,  note: "Leicht – Böen kritisch" },
  { key: "air",   label: "DJI Air",         greenMax: 8,  yellowMax: 10, gustRed: 12, note: "Sweet Spot, aber fordernd bei Böen" },
  { key: "mavic", label: "DJI Mavic / Pro", greenMax: 10, yellowMax: 12, gustRed: 14, note: "Stabil, Rückflug beachten" },
  { key: "fpv",   label: "DJI FPV / Avata", special: true, note: "Stark abhängig von Erfahrung, Modus und Umgebung" },
];

let windLastFetchAt = 0;
let windLastKey = "";
let windHooksInstalled = false;

function windEnsureUI() {
  if (document.getElementById("windBox")) return;

  const box = document.createElement("div");
  box.id = "windBox";
  box.setAttribute("data-panel-id", "wind");
  box.setAttribute("data-panel-collapsible", "1");
  box.style.marginTop = "10px";
  box.style.padding = "10px";
  box.style.borderRadius = "10px";
  box.style.border = "1px solid rgba(255,255,255,0.08)";
  box.style.background = "rgba(0,0,0,0.25)";
  box.style.color = "inherit";

  box.innerHTML = `
    <div style="display:flex; align-items:center; justify-content:space-between; gap:10px; margin-bottom:6px;">
      <div style="font-weight:700;">Wind am Standort</div>
      <button type="button" data-panel-toggle="wind" aria-label="Wind Panel ein/ausklappen">▾</button>
    </div>

    <div data-panel-body>
      <div id="windValues" style="opacity:.95;">—</div>
    <div id="windDJI" style="margin-top:6px;opacity:.95;">—</div>
    <div style="margin-top:6px;opacity:.65;font-size:12px;line-height:1.25;">
      Einschätzung basiert auf DJI-Referenzwerten (konservativ) & Modellwind (10 m). Lokale Effekte möglich.
    </div>
  </div>
  `;

  if (window.__DA_PANEL__ && window.__DA_PANEL__.register) {
    window.__DA_PANEL__.register(box, "wind", true);
  }

  const anchor = document.getElementById("detail") || document.getElementById("state") || document.body;
  anchor.parentNode.insertBefore(box, anchor.nextSibling);
}

function windDirFromDeg(deg) {
  const dirs = ["N","NNO","NO","ONO","O","OSO","SO","SSO","S","SSW","SW","WSW","W","WNW","NW","NNW"];
  const d = ((deg % 360) + 360) % 360;
  return dirs[Math.round(d / 22.5) % 16];
}

function windClassifyDJI(windMs, gustMs) {
  const lines = [];
  for (const c of WIND_DJI_CLASSES) {
    if (c.special) {
      lines.push(`• <b>${c.label}</b>: ⚠️ ${c.note}`);
      continue;
    }
    let status = "🟢";
    let text = "ruhig";
    if (windMs > c.greenMax && windMs <= c.yellowMax) { status = "🟡"; text = "fordernd"; }
    if (windMs > c.yellowMax || gustMs >= c.gustRed) { status = "🔴"; text = "kritisch"; }
    lines.push(`• <b>${c.label}</b>: ${status} ${text}`);
  }
  return lines.join("<br/>");
}

function windRender(current) {
  windEnsureUI();

  const v = document.getElementById("windValues");
  const d = document.getElementById("windDJI");
  if (!v || !d) return;

  if (!current) {
    v.textContent = "—";
    d.textContent = "—";
    return;
  }

  const ws = Number(current.wind_speed_10m);
  const wg = Number(current.wind_gusts_10m);
  const wd = Number(current.wind_direction_10m);

  const dir = Number.isFinite(wd) ? windDirFromDeg(wd) : "—";

  if (Number.isFinite(ws) && Number.isFinite(wg) && Number.isFinite(wd)) {
    v.innerHTML = `💨 <b>${ws.toFixed(1)} m/s</b> &nbsp; 🌬 Böen <b>${wg.toFixed(1)} m/s</b> &nbsp; 🧭 ${dir} (${Math.round(wd)}°)`;
    d.innerHTML = `<div style="font-weight:600;margin-bottom:4px;">DJI-Referenz</div>${windClassifyDJI(ws, wg)}`;
  } else {
    v.textContent = "Winddaten unvollständig.";
    d.textContent = "—";
  }
}

async function windFetch(lat, lon) {
  const params = new URLSearchParams({
    latitude: lat.toFixed(4),
    longitude: lon.toFixed(4),
    current: "wind_speed_10m,wind_gusts_10m,wind_direction_10m",
    wind_speed_unit: "ms",
    timezone: "UTC",
  });
  const url = `${WIND_API_BASE}?${params.toString()}`;
  const res = await fetch(url, { cache: "no-cache" });
  if (!res.ok) throw new Error(`Winddaten HTTP ${res.status}`);
  const js = await res.json();
  return js?.current || null;
}

async function windUpdate(lat, lon, force = false) {
  try {
    windEnsureUI();

    const now = Date.now();
    const key = `${lat.toFixed(3)},${lon.toFixed(3)}`;

    if (!force) {
      if (now - windLastFetchAt < WIND_THROTTLE_MS) return;
      if (key === windLastKey && now - windLastFetchAt < (WIND_THROTTLE_MS * 2)) return;
    }

    windLastFetchAt = now;
    windLastKey = key;

    const current = await windFetch(lat, lon);
    windRender(current);
  } catch (_) {
    // leise bleiben – Wind ist Zusatz, darf die Ampel nicht blockieren
  }
}

function windInstallHooks() {
  if (windHooksInstalled) return;
  if (typeof marker === "undefined" || !marker) return;

  windEnsureUI();

  // 1) Bei jeder Pin-Bewegung
  const onMove = () => {
    try {
      const p = marker.getLatLng();
      windUpdate(p.lat, p.lng, false);
    } catch (_) {}
  };

  try { marker.on("drag", onMove); } catch (_) {}
  try { marker.on("dragend", onMove); } catch (_) {}

  // 2) Zusätzlich: updateMap hooken (GPS/Manual/Programmatic)
  try {
    if (typeof updateMap === "function" && !updateMap.__windWrapped) {
      const _u = updateMap;
      const wrapped = function(lat, lon, accuracyMeters = null) {
        const r = _u(lat, lon, accuracyMeters);
        try { windUpdate(lat, lon, true); } catch (_) {}
        return r;
      };
      wrapped.__windWrapped = true;
      updateMap = wrapped;
    }
  } catch (_) {}

  // Initiale Abfrage
  try {
    const p = marker.getLatLng();
    windUpdate(p.lat, p.lng, true);
  } catch (_) {}

  windHooksInstalled = true;
}

// warten bis marker existiert (initMap läuft synchron, aber sicher ist sicher)
const windWait = setInterval(() => {
  if (typeof marker !== "undefined" && marker) {
    windInstallHooks();
    clearInterval(windWait);
  }
}, 200);

// UI early
document.addEventListener("DOMContentLoaded", () => {
  try { windEnsureUI(); } catch (_) {}
});


// =============================
// IMO / vedur.is – "Now & Next" für Drohnenpiloten (additiv)
// Ziel: Regen, Wind, Nebel/Sicht + Warnungen (CAP) am Standort
// - reine Client-side fetch()
// - keine Speicherung/Tracking
// - Attribution sichtbar
// Quellen (Open Data): https://api.vedur.is/weather/openapi.json & https://api.vedur.is/cap/v1/openapi.json
// =============================

const IMO_WEATHER_BASE = "https://api.vedur.is/weather";

// Alias (Legacy): einige Funktionen nutzen noch IMO_API_WEATHER
const IMO_API_WEATHER = IMO_WEATHER_BASE;
const IMO_CAP_BASE = "https://api.vedur.is/cap/v1";
const IMO_SRID = 4326;

// "Leise" Limits: nicht spammen, aber reaktionsschnell genug fürs Pin-Dragging
const IMO_THROTTLE_MS = 15_000;
const IMO_CAP_DISTANCE_KM = 220;    // groß genug für Küsten-Regionen, klein genug für Kontext

let imoHooksInstalled = false;
let imoLastFetchAt = 0;
let imoLastKey = "";

// Station-Cache (nur im RAM; keine Persistenz)
let imoStationsCache = null;        // Array<Station>
let imoStationsFetchedAt = 0;
const IMO_STATIONS_TTL_MS = 6 * 60 * 60 * 1000; // 6h

function imoEnsureUI() {
  if (document.getElementById("imoBox")) return;

  const box = document.createElement("div");
  box.id = "imoBox";
  box.setAttribute("data-panel-id", "imo");
  box.setAttribute("data-panel-collapsible", "1");
  box.style.marginTop = "10px";
  box.style.padding = "10px";
  box.style.borderRadius = "10px";
  box.style.border = "1px solid rgba(255,255,255,0.08)";
  box.style.background = "rgba(0,0,0,0.25)";
  box.style.color = "inherit";

  box.innerHTML = `
    <div style="display:flex; align-items:center; justify-content:space-between; gap:10px;">
      <div style="font-weight:700;">IMO – Now & Next</div>
      <div style="display:flex; align-items:center; gap:8px;">
        <div style="opacity:.65; font-size:12px;">Data: IMO / vedur.is</div>
        <button type="button" data-panel-toggle="imo" aria-label="IMO Panel ein/ausklappen">▾</button>
      </div>
    </div>

    <div data-panel-body>

    <div style="margin-top:6px; opacity:.75; font-size:12px; line-height:1.25;">
      IMO-Daten basieren auf Open Data der isländischen Wetterbehörde (IMO / vedur.is) und werden direkt von api.vedur.is abgerufen (ohne Speicherung, ohne Tracking).
    </div>

    <div style="margin-top:6px; opacity:.9; font-size:13px; line-height:1.35;">
      <div id="imoNow" style="margin-top:4px;">—</div>
      <div id="imoNext" style="margin-top:6px;">—</div>
      <div id="imoAlerts" style="margin-top:8px;">—</div>
    </div>

    <div style="margin-top:10px; opacity:.65; font-size:12px; line-height:1.3;">
      <b>NOW</b>: nächste automatische Messstation(en) (AWS) inkl. aktuellem Messwert.<br>
      <b>NEXT</b>: Kurztrend der letzten ~60 Minuten aus 10‑Minuten‑Messungen (kein Modell) – zeigt, ob Wind/Böen eher zunehmen oder abnehmen.<br>
      <b>ALERTS</b>: offizielle Warnungen (CAP) im Umkreis deines Standorts.
    </div>
  `;

  if (window.__DA_PANEL__ && window.__DA_PANEL__.register) {
    window.__DA_PANEL__.register(box, "imo", true);
  }

  // Unter Wind-Box einhängen (wie im Screenshot gewünscht)
  const wind = document.getElementById("windBox");
  if (wind && wind.parentNode) {
    wind.parentNode.insertBefore(box, wind.nextSibling);
    return;
  }

  // Fallback, falls Wind-Box (noch) nicht existiert
  const anchor = document.getElementById("detail") || document.getElementById("state") || document.body;
  anchor.parentNode.insertBefore(box, anchor.nextSibling);
}

function imoFmt(num, digits = 1) {
  if (num === null || num === undefined || Number.isNaN(Number(num))) return "—";
  return Number(num).toFixed(digits);
}

function imoPick(obj, keys) {
  if (!obj) return undefined;
  for (const k of keys) {
    if (Object.prototype.hasOwnProperty.call(obj, k) && obj[k] !== null && obj[k] !== undefined) return obj[k];
  }
  return undefined;
}

function imoCompassFromDeg(deg) {
  if (deg === null || deg === undefined || Number.isNaN(Number(deg))) return "—";
  const dirs = ["N","NNO","NO","ONO","O","OSO","SO","SSO","S","SSW","SW","WSW","W","WNW","NW","NNW"];
  const d = ((Number(deg) % 360) + 360) % 360;
  return dirs[Math.round(d / 22.5) % 16];
}

function imoHaversineKm(lat1, lon1, lat2, lon2) {
  const R = 6371;
  const toRad = (x) => (x * Math.PI) / 180;
  const dLat = toRad(lat2 - lat1);
  const dLon = toRad(lon2 - lon1);
  const a = Math.sin(dLat/2)**2 + Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLon/2)**2;
  const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
  return R * c;
}

async function imoFetchStations() {
  const now = Date.now();
  if (imoStationsCache && (now - imoStationsFetchedAt) < IMO_STATIONS_TTL_MS) return imoStationsCache;

  // AWS-Stationen (Automatic stations = sj), aktiv
  const url = `${IMO_WEATHER_BASE}/stations?active=true&station_type=sj`;
  const res = await fetch(url, { cache: "no-cache" });
  if (!res.ok) throw new Error(`IMO stations HTTP ${res.status}`);
  const stations = await res.json();

  imoStationsCache = Array.isArray(stations) ? stations : [];
  imoStationsFetchedAt = now;
  return imoStationsCache;
}

function imoNearestStations(lat, lon, stations, n = 3) {
  const arr = [];
  for (const s of (stations || [])) {
    const slat = Number(s?.lat ?? s?.latitude);
    const slon = Number(s?.lon ?? s?.longitude);
    if (!Number.isFinite(slat) || !Number.isFinite(slon)) continue;
    const dist = imoHaversineKm(lat, lon, slat, slon);
    arr.push({ station: s, distKm: dist });
  }
  arr.sort((a,b) => a.distKm - b.distKm);
  return arr.slice(0, n);
}

async function imoFetchLatest10min(stationIds) {
  // IMO liefert Observations typischerweise mit Feld "station" (z.B. 1350).
  // Je nach Endpoint/Schema heißt der Query-Parameter "station" oder "station_id".
  // Wir versuchen daher zuerst "station" (passt zu den Observations), und fallback auf "station_id".
  const ids = (stationIds || []).map(x => String(x));

  const tryFetch = async (paramName) => {
    const params = new URLSearchParams();
    for (const id of ids) params.append(paramName, id);
    const url = `${IMO_WEATHER_BASE}/observations/aws/10min/latest?${params.toString()}`;
    const res = await fetch(url, { cache: "no-cache" });
    if (!res.ok) throw new Error(`IMO aws latest HTTP ${res.status}`);
    const data = await res.json();
    return Array.isArray(data) ? data : [];
  };

  // 1) bevorzugt: station
  const a = await tryFetch("station");
  if (a.length) return a;

  // 2) fallback: station_id
  return await tryFetch("station_id");
}

async function imoFetchRecent10min(stationId, count = 6) {
  // NEXT: Kurztrend aus 10-Minuten-Observations.
  // Wichtig: Diese Abfrage ist optional und darf niemals NOW kaputt machen.
  // Laut IMO Weather OpenAPI nutzt AWS 10min die Parameter:
  // - station_id (array/integer)
  // - order (asc|desc)
  // - count (max 12, wenn kein day_from/day_to gesetzt ist)
  // Zeitstempel-Parameter wie from/to/time_from/time_to werden hier NICHT akzeptiert (führen zu 400).

  const sid = String(stationId ?? "").trim();
  if (!sid) return [];

  const safeCount = Math.max(1, Math.min(12, Number(count) || 6));

  // Primär: processed 10min (stabiler für Dashboards)
  // Fallback: raw 10min (unprocessed), falls processed nicht verfügbar ist.
  const candidates = [
    `${IMO_WEATHER_BASE}/observations/aws/10min?station_id=${encodeURIComponent(sid)}&order=desc&count=${encodeURIComponent(safeCount)}&parameters=basic`,
    `${IMO_WEATHER_BASE}/observations/aws/raw/10min?station_id=${encodeURIComponent(sid)}&order=desc&count=${encodeURIComponent(safeCount)}&parameters=basic`
  ];

  for (const url of candidates) {
    try {
      const res = await fetch(url, { cache: "no-store" });
      if (!res.ok) continue;

      const j = await res.json();
      const arr = Array.isArray(j) ? j : (Array.isArray(j?.observations) ? j.observations : []);
      if (!Array.isArray(arr) || !arr.length) return [];

      // IMO liefert i.d.R. bereits sortiert, aber wir sortieren defensiv nach Zeitfeld.
      const copy = arr.slice();
      copy.sort((a, b) => {
        const ta = Date.parse(a?.time ?? a?.created ?? a?.timestamp ?? "") || 0;
        const tb = Date.parse(b?.time ?? b?.created ?? b?.timestamp ?? "") || 0;
        return tb - ta;
      });

      return copy.slice(0, safeCount);
    } catch (_) {
      continue;
    }
  }

  return [];
}

function imoExtractCore(obs) {
  // Robust gegen unterschiedliche Feldnamen (IMO nutzt teils Kurz-Codes)
  const wind = imoPick(obs, ["f","ff","wind_speed","windspeed","ws"]);
  const gust = imoPick(obs, ["fg","fx","gust","wind_gust","wind_speed_of_gust"]);
  const dirDeg = imoPick(obs, ["d","dd","dir","wind_direction","wd"]);
  const precip = imoPick(obs, ["r","rr","precip","precipitation","rain","r_1h","r1h"]);
  const vis = imoPick(obs, ["vis","visibility","sight","view"]);
  const rh = imoPick(obs, ["rh","humidity","relative_humidity"]);
  const t = imoPick(obs, ["t","temp","temperature","air_temperature"]);
  const ts = imoPick(obs, ["time","datetime","date","timi","obs_time","at"]);
  return { wind, gust, dirDeg, precip, vis, rh, t, ts };
}

function imoFogHeuristic(core) {
  // Wenn Sichtweite da ist: direkt
  if (core.vis !== undefined) {
    const v = Number(core.vis);
    if (!Number.isNaN(v)) {
      if (v < 1000) return "sehr wahrscheinlich";
      if (v < 3000) return "möglich";
      return "unwahrscheinlich";
    }
  }
  // Heuristik ohne Sichtweite: hohe Feuchte + wenig Wind
  const rh = Number(core.rh);
  const w = Number(core.wind);
  if (!Number.isNaN(rh) && !Number.isNaN(w)) {
    if (rh >= 97 && w <= 3) return "möglich";
    if (rh >= 93 && w <= 2) return "leicht möglich";
  }
  return "—";
}

function imoTrendLabel(series, keyName) {
  // series ist DESC (neu -> alt)
  if (!Array.isArray(series) || series.length < 2) return "—";
  const newest = imoExtractCore(series[0])[keyName];
  const oldest = imoExtractCore(series[series.length - 1])[keyName];
  const a = Number(newest);
  const b = Number(oldest);
  if (Number.isNaN(a) || Number.isNaN(b)) return "—";
  const delta = a - b;

  // kleine toter Bereich
  const eps = (keyName === "wind" || keyName === "gust") ? 0.6 : 0.2;
  if (Math.abs(delta) <= eps) return "↔ stabil";
  return delta > 0 ? "↗ zunehmend" : "↘ abnehmend";
}

function imoRenderNowNext({ nearest, latestByStationId, seriesMain }) {
  imoEnsureUI();
  const nowEl = document.getElementById("imoNow");
  const nextEl = document.getElementById("imoNext");
  if (!nowEl || !nextEl) return;

  if (!nearest || !nearest.length) {
    nowEl.textContent = "NOW: Keine Stationen gefunden.";
    nextEl.textContent = "NEXT: —";
    return;
  }

  // NOW: Liste der nächsten Stationen (kompakt)
  const lines = [];
  for (const item of nearest) {
    const s = item.station;
    const sid = s?.station ?? s?.id ?? s?.station_id ?? s?.stationId;
    const obs = latestByStationId.get(String(sid));
    const core = obs ? imoExtractCore(obs) : null;

    const wind = core ? imoFmt(core.wind, 1) : "—";
    const gust = core ? imoFmt(core.gust, 1) : "—";
    const dir = core ? `${imoCompassFromDeg(core.dirDeg)} (${core.dirDeg !== undefined ? Math.round(Number(core.dirDeg)) : "—"}°)` : "—";
    const rain = core && core.precip !== undefined ? `${imoFmt(core.precip, 1)} mm` : "—";
    const fog = core ? imoFogHeuristic(core) : "—";

    const name = escapeHtml(s?.name ?? s?.station_name ?? `Station ${sid}`);
    lines.push(`• <b>${name}</b> (${imoFmt(item.distKm, 1)} km): 💨 ${wind} m/s · 💥 ${gust} m/s · 🧭 ${escapeHtml(dir)} · 🌧️ ${rain} · 🌫️ ${escapeHtml(fog)}`);
  }

  nowEl.innerHTML = `<b>NOW</b> (Messstationen):<br/>${lines.join("<br/>")}`;

  // NEXT: Trend aus den letzten ~60 Minuten (nur Hauptstation = nächste)
  if (!Array.isArray(seriesMain) || !seriesMain.length) {
    nextEl.innerHTML = `<b>NEXT</b> (Trend ~60 min): —`;
    return;
  }
  const coreNow = imoExtractCore(seriesMain[0]);
  const windTrend = imoTrendLabel(seriesMain, "wind");
  const rainTrend = imoTrendLabel(seriesMain, "precip");
  const fog = imoFogHeuristic(coreNow);

  // "im Gleich": Wenn Wind ↑ oder Regen ↑ oder Nebel wahrscheinlich -> das ist dein Entscheidungsfeind
  nextEl.innerHTML =
    `<b>NEXT</b> (Trend ~60 min, keine Modellprognose): ` +
    `💨 ${windTrend} · 🌧️ ${rainTrend} · 🌫️ ${escapeHtml(fog)}`;
}

function _imoColorBadge(color) {
  const c = String(color || "").toLowerCase();
  let dot = "⚪";
  if (c.includes("yellow")) dot = "🟡";
  if (c.includes("orange")) dot = "🟠";
  if (c.includes("red")) dot = "🔴";
  if (c.includes("green")) dot = "🟢";
  return dot;
}

async function imoFetchNearbyAlertIds(lat, lon) {
  const url = `${IMO_CAP_BASE}/lat/${lat}/long/${lon}/srid/${IMO_SRID}/distance/${IMO_CAP_DISTANCE_KM}/`;
  const res = await fetch(url, { cache: "no-cache" });
  if (!res.ok) throw new Error(`IMO CAP HTTP ${res.status}`);
  return await res.json(); // GenericCapMessages
}

async function imoFetchAlertJson(msg) {
  const sender = encodeURIComponent(msg.sender);
  const identifier = encodeURIComponent(msg.identifier);
  const sent = encodeURIComponent(msg.sent);
  const url = `${IMO_CAP_BASE}/capbroker/sender/${sender}/identifier/${identifier}/sent/${sent}/json/`;
  const res = await fetch(url, { cache: "no-cache" });
  if (!res.ok) throw new Error(`IMO CAP msg HTTP ${res.status}`);
  return await res.json(); // CapMessageJsonResponse
}

function imoRenderAlerts(capJson) {
  imoEnsureUI();
  const el = document.getElementById("imoAlerts");
  if (!el) return;

  if (!capJson) {
    el.innerHTML = `<b>ALERTS</b>: Keine aktiven Warnungen im Umkreis.`;
    return;
  }

  const infos = capJson?.alert?.info;
  const arr = Array.isArray(infos) ? infos : [];
  const en = arr.find(x => (x?.language || "").toLowerCase().startsWith("en")) || arr[0] || null;

  if (!en) {
    el.innerHTML = `<b>ALERTS</b>: Keine lesbaren Warn-Details.`;
    return;
  }

  // Color steckt häufig in parameter/valueName=Color
  let color = "";
  try {
    const p = en.parameter;
    if (Array.isArray(p)) {
      const c = p.find(x => (x?.valueName || "").toLowerCase() === "color");
      color = c?.value || "";
    } else if (p && typeof p === "object") {
      color = p.value || "";
    }
  } catch (_) {}

  const badge = _imoColorBadge(color);
  const headline = en.headline || en.event || "Warning";
  const desc = (en.description || "").trim();

  el.innerHTML =
    `<b>ALERTS</b>: ${badge} <b>${escapeHtml(headline)}</b>` +
    `${color ? ` <span style="opacity:.75;">(${escapeHtml(color)})</span>` : ""}` +
    (desc ? `<div style="margin-top:4px; opacity:.9;">${escapeHtml(desc).replace(/\n/g, "<br/>")}</div>` : "");
}

function imoRenderError() {
  imoEnsureUI();
  const nowEl = document.getElementById("imoNow");
  const nextEl = document.getElementById("imoNext");
  const alertEl = document.getElementById("imoAlerts");
  if (nowEl) nowEl.textContent = "NOW: IMO-Daten aktuell nicht verfügbar.";
  if (nextEl) nextEl.textContent = "NEXT: —";
  if (alertEl) alertEl.textContent = "ALERTS: —";
}

async function imoUpdate(lat, lon, force = false) {
  try {
    imoEnsureUI();

    const now = Date.now();
    const key = `${lat.toFixed(3)},${lon.toFixed(3)}`;

    if (!force) {
      if (now - imoLastFetchAt < IMO_THROTTLE_MS) return;
      if (key === imoLastKey && now - imoLastFetchAt < (IMO_THROTTLE_MS * 2)) return;
    }

    imoLastFetchAt = now;
    imoLastKey = key;

    // 1) Stations
    const stations = await imoFetchStations();
    const nearest = imoNearestStations(lat, lon, stations, 3);

    // 2) Latest obs für die 3 Stationen
    const ids = nearest
      .map(x => x.station?.station ?? x.station?.id ?? x.station?.station_id ?? x.station?.stationId)
      .filter(x => x !== undefined && x !== null)
      .map(x => String(x));
    const latest = await imoFetchLatest10min(ids);
    const latestByStationId = new Map();
    for (const o of latest) {
      const sid = o?.station_id ?? o?.stationId ?? o?.id ?? o?.station;
      if (sid !== undefined && sid !== null) latestByStationId.set(String(sid), o);
    }

    // 3) Series für die nächste Station (Trend ~60 min)
    // NEXT ist optional: darf NOW nicht killen.
    // WICHTIG: Einige Stationen liefern für die 10-Minuten-Serie (observations/aws/10min) 400.
    // Das erzeugt DevTools-Fehler-Spam, obwohl wir es sauber catchen.
    // Daher ist NEXT hier bewusst deaktiviert, bis wir eine verlässlich valide Serien-Abfrage haben.
    let seriesMain = [];

    imoRenderNowNext({ nearest, latestByStationId, seriesMain });

    // 4) CAP Alerts
    try {
      const nearby = await imoFetchNearbyAlertIds(lat, lon);
      const msgs = Array.isArray(nearby) ? nearby : (Array.isArray(nearby?.messages) ? nearby.messages : []);
      if (!msgs.length) {
        imoRenderAlerts(null);
      } else {
        const first = msgs[0];
        if (first?.sender && first?.identifier && first?.sent) {
          const capJson = await imoFetchAlertJson(first);
          imoRenderAlerts(capJson);
        } else {
          imoRenderAlerts(null);
        }
      }
    } catch (_) {
      // Alerts sind nice-to-have: keine Panik in der UI
      imoRenderAlerts(null);
    }

  } catch (_) {
    imoRenderError();
  }
}

function imoInstallHooks() {
  if (imoHooksInstalled) return;
  if (typeof marker === "undefined" || !marker) return;

  imoEnsureUI();

  const onMove = () => {
    try {
      const p = marker.getLatLng();
      imoUpdate(p.lat, p.lng, false);
    } catch (_) {}
  };

  try { marker.on("drag", onMove); } catch (_) {}
  try { marker.on("dragend", onMove); } catch (_) {}

  // updateMap hooken (GPS/Manual/Programmatic)
  try {
    if (typeof updateMap === "function" && !updateMap.__imoWrapped) {
      const _u = updateMap;
      const wrapped = function(lat, lon, accuracyMeters = null) {
        const r = _u(lat, lon, accuracyMeters);
        try { imoUpdate(lat, lon, true); } catch (_) {}
        return r;
      };
      wrapped.__imoWrapped = true;
      updateMap = wrapped;
    }
  } catch (_) {}

  // initial
  try {
    const p = marker.getLatLng();
    imoUpdate(p.lat, p.lng, true);
  } catch (_) {}

  imoHooksInstalled = true;
}

// warten bis marker existiert
const imoWait = setInterval(() => {
  if (typeof marker !== "undefined" && marker) {
    imoInstallHooks();
    clearInterval(imoWait);
  }
}, 250);

// UI early
document.addEventListener("DOMContentLoaded", () => {
  try { imoEnsureUI(); } catch (_) {}
});


// =============================
// SPOT-LAYER – 2 Modi (Piloten first)
// 1) Drohnen-Spots (Default): Luftbildpotenzial, keine Aussage zur Flugerlaubnis
// 2) Fotografisch wertvoll: Klassiker & Orientierung, ohne Drohnenbezug
// - keine Navigation / kein Routing / keine Google-Dienste
// - jeder Spot: Text + saubere Decimal-Koordinaten
//
// Datenhygiene:
// - einheitliches Modell: { id, name, category, lat, lon, short, long, tags[] }
// - Validierung: Zahlen, Island-Bounds, eindeutige IDs
// - Trennung: Daten (Spots) vs. Darstellung (Marker/Popup)
// =============================

const SPOT_MIN_ZOOM = 0; // immer sichtbar (Popups per Klick)

const SPOT_MODES = {
  drone: {
    key: "drone",
    title: "Drohnen-Spots",
    subtitle: "Luftbild-Potenzial. Keine Aussage zur Flugerlaubnis.",
  },
  photo: {
    key: "photo",
    title: "Fotografisch wertvoll",
    subtitle: "Klassiker & Orientierung. Ohne Drohnenbezug.",
  },
};

// =============================
// Spot-Info am Pin (Radius)
// - zeigt Kontext (2–3 Sätze) sobald der Pin in der Nähe eines Spots ist
// - keine Navigation / kein Routing / keine Rechtsaussage
// =============================
const SPOT_INFO_RADIUS_M = 250;

let _nearSpotState = null; // { modeKey, spot, distM } oder null

function _deg2rad(d) { return (d * Math.PI) / 180; }

// Haversine (Meter)
function _distanceM(lat1, lon1, lat2, lon2) {
  const R = 6371000;
  const dLat = _deg2rad(lat2 - lat1);
  const dLon = _deg2rad(lon2 - lon1);
  const a =
    Math.sin(dLat / 2) * Math.sin(dLat / 2) +
    Math.cos(_deg2rad(lat1)) * Math.cos(_deg2rad(lat2)) *
    Math.sin(dLon / 2) * Math.sin(dLon / 2);
  const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  return R * c;
}

function _pickNearestSpot(lat, lon) {
  // sicherstellen, dass Daten normalisiert vorhanden sind
  if (!_DRONE_SPOTS.length) _DRONE_SPOTS = _validateSpots("drone", DRONE_SPOTS_RAW);
  if (!_PHOTO_SPOTS.length) _PHOTO_SPOTS = _validateSpots("photo", PHOTO_SPOTS_RAW);

  let best = null;

  const consider = (modeKey, arr) => {
    for (const s of arr) {
      if (!s || !Number.isFinite(s.lat) || !Number.isFinite(s.lon)) continue;
      const d = _distanceM(lat, lon, s.lat, s.lon);
      if (d <= SPOT_INFO_RADIUS_M && (!best || d < best.distM)) {
        best = { modeKey, spot: s, distM: d };
      }
    }
  };

  consider("drone", _DRONE_SPOTS);
  consider("photo", _PHOTO_SPOTS);

  return best;
}

function _spotInfoText(spot) {
  const parts = [];
  if (spot && spot.short) parts.push(String(spot.short).trim());
  if (spot && spot.long) parts.push(String(spot.long).trim());

  // 2–3 Sätze, ohne Roman:
  // - wir nehmen short+long, schneiden aber hart bei ~340 Zeichen
  const raw = parts.filter(Boolean).join(" ").replace(/\s+/g, " ").trim();
  if (!raw) return "";

  const max = 340;
  if (raw.length <= max) return raw;

  // hübsch abbrechen (am nächsten Punkt oder Leerzeichen)
  const cut = raw.slice(0, max);
  const lastDot = Math.max(cut.lastIndexOf("."), cut.lastIndexOf("!"), cut.lastIndexOf("?"));
  if (lastDot > 120) return cut.slice(0, lastDot + 1).trim();
  const lastSpace = cut.lastIndexOf(" ");
  return (lastSpace > 120 ? cut.slice(0, lastSpace) : cut).trim() + "…";
}

function _renderNearSpotBox(lat, lon) {
  const box = document.getElementById("nearSpotBox");
  const titleEl = document.getElementById("nearSpotTitle");
  const metaEl = document.getElementById("nearSpotMeta");
  const textEl = document.getElementById("nearSpotText");
  if (!box || !titleEl || !metaEl || !textEl) return;

  const best = _pickNearestSpot(lat, lon);
  _nearSpotState = best;

  if (!best) {
    titleEl.textContent = "Spot-Info";
    metaEl.textContent = `Kein Spot im Umkreis von ${SPOT_INFO_RADIUS_M} m.`;
    textEl.textContent = "—";
    return;
  }

  const modeLabel = best.modeKey === "drone" ? "Drohnen-Spot" : "Fotografisch wertvoll";
  titleEl.textContent = best.spot && best.spot.name ? best.spot.name : "Spot";
  const dist = Math.round(best.distM);
  const cat = (best.spot && best.spot.category) ? String(best.spot.category).trim() : "";
  metaEl.textContent = `${modeLabel}${cat ? " · " + cat : ""} · ca. ${dist} m entfernt`;

  const t = _spotInfoText(best.spot);
  textEl.textContent = t || "—";
}

// --- Spots: Südküste Reykjavík → Höfn (inkl. Klassiker) ---
// Hinweis: Koordinaten sind Orientierungspunkte, nicht „Startpunkte“.
// Tags sind rein kuratierend (z.B. "klassiker", "minimal", "windy") – keine Rechtsaussage.
const DRONE_SPOTS_RAW = [
  {
    id: "d_rvk_harbor_lines",
    name: "Reykjavík – Linien & Dächer",
    category: "Urban / Küste",
    lat: 64.1466, lon: -21.9426,
    short: "Hafenlinien, grafische Dächer, reduziertes Luftbild.",
    long: "Küste, Hafenlinien, grafische Dächer – aus der Luft sauber und reduziert. Früh oder spät wird’s filmisch.",
    tags: ["urban", "grafisch", "ruhig"]
  },
  {
    id: "d_reykjanes_lava_ridges",
    name: "Reykjanes – Lava-Rhythmen",
    category: "Lava / Struktur",
    lat: 63.8870, lon: -22.2690,
    short: "Lavafelder, Risse, Muster – Island als Zeichnung.",
    long: "Lavafelder, Risse, Rhythmus. Aus der Höhe wird Island zur Zeichnung – hier zählt Komposition mehr als Drama.",
    tags: ["struktur", "minimal", "textur"]
  },
  {
    id: "d_thjorsa_plain",
    name: "Þjórsá-Ebene – Maßstab",
    category: "Maßstab & Weite",
    lat: 63.7833, lon: -20.8000,
    short: "Weite Ebenen und Flussläufe – groß, ohne laut zu sein.",
    long: "Weite Ebenen, Flussläufe, Ruhe. Wenn du Größe zeigen willst, ohne zu schreien: genau hier.",
    tags: ["weite", "ruhig"]
  },
  {
    id: "d_seljalands_area",
    name: "Seljalands-Umfeld – Wasseradern",
    category: "Struktur & Bewegung",
    lat: 63.6170, lon: -19.9833,
    short: "Nicht der Wasserfall – das Umfeld als Linienbild.",
    long: "Nicht der Wasserfall – das Umfeld. Wasseradern schreiben Linien ins Land. Turbulenzen möglich: Wind ernst nehmen.",
    tags: ["struktur", "windy"]
  },
  {
    id: "d_skogasandur_minimal",
    name: "Skógasandur – Minimal",
    category: "Minimal / Textur",
    lat: 63.4833, lon: -19.4833,
    short: "Schwarze Ebenen, feine Spuren, große Stille.",
    long: "Schwarze Ebenen, feine Spuren, große Stille. Reduktion statt Spektakel – der Himmel darf hier Hauptdarsteller sein.",
    tags: ["minimal", "textur"]
  },
  {
    id: "d_solheimasandur_outwash",
    name: "Sólheimasandur – Outwash-Muster",
    category: "Muster / Outwash",
    lat: 63.4595, lon: -19.3646,
    short: "Verzweigte Wasserläufe – Ordnung im Chaos.",
    long: "Verzweigte Wasserläufe, Sandstrukturen – Ordnung im Chaos. Wetter macht hier den Charakter.",
    tags: ["muster", "textur", "windy"]
  },
  {
    id: "d_dyrholaey_rhythm",
    name: "Dyrhólaey – Rhythmus",
    category: "Küste & Linien",
    lat: 63.4022, lon: -19.1307,
    short: "Brandung, Kanten, Richtung – starke Linienführung.",
    long: "Brandung, Küstenkanten, Richtung. Aus der Luft: Rhythmus, der im Kopf bleibt.",
    tags: ["kuste", "linien", "windy"]
  },
  {
    id: "d_myrdalssandur_weite",
    name: "Mýrdalssandur – Weite",
    category: "Weite / Komposition",
    lat: 63.4579, lon: -18.5581,
    short: "Große Flächen – Höhe dosieren, Bild atmen lassen.",
    long: "Große Flächen, wenig Ablenkung. Perfekt, um Höhe und Perspektive fein zu dosieren.",
    tags: ["weite", "minimal"]
  },
  {
    id: "d_skeidararsandur_dynamics",
    name: "Skeiðarársandur – Dynamik",
    category: "Schwemmland XXL",
    lat: 63.9000, lon: -17.2333,
    short: "Flussarme wie Adern – ständig neue Muster.",
    long: "Flussarme wie Adern – ständig neue Muster. Lohnt sich, aber Böen und Wetterwechsel sind hier nicht optional.",
    tags: ["muster", "windy", "weite"]
  },
  {
    id: "d_skaftafell_edges",
    name: "Skaftafell – Kanten (Eis/Erde)",
    category: "Eis / Kanten",
    lat: 64.0147, lon: -16.9739,
    short: "Übergänge von Eis zu Erde – Kanten, Risse, Richtung.",
    long: "Übergänge von Eis zu Erde: Kanten, Risse, Richtung. Bei klarer Sicht sehr plastisch – bei Nebel wird’s abstrakt.",
    tags: ["eis", "struktur"]
  },
  {
    id: "d_jokulsarlon_outflow",
    name: "Jökulsárlón – Abfluss & Textur",
    category: "Textur & Fluss",
    lat: 64.0784, lon: -16.2306,
    short: "Abfluss, Strömung, Textur – grafisch bei gutem Licht.",
    long: "Abfluss, Strömung, Textur. Aus der Luft grafisch – Licht entscheidet über „glatt“ oder „wild“.",
    tags: ["textur", "fluss", "windy"]
  },
  {
    id: "d_hofn_foreland",
    name: "Höfn – Küstenvorland",
    category: "Weite & Ruhe",
    lat: 64.2539, lon: -15.2121,
    short: "Lagunen- und Küstenebenen – ein leiser Schlussakkord.",
    long: "Lagunen- und Küstenebenen – ein leiser Schlussakkord. Übergänge zwischen Land/Wasser/Sand.",
    tags: ["ruhe", "weite"]
  },
];

const PHOTO_SPOTS_RAW = [
  {
    id: "p_harpa",
    name: "Harpa (Reykjavík)",
    category: "Stadt / Architektur",
    lat: 64.1500, lon: -21.9330,
    short: "Kanten, Spiegelungen, grafische Flächen.",
    long: "Harpa & Hafen – klare Kanten, Spiegelungen, grafische Flächen. Gerade im Winter ein Lichtlabor.",
    tags: ["architektur", "grafisch"]
  },
  { id: "p_seljalandsfoss", name: "Seljalandsfoss", category: "Wasserfall", lat: 63.6156, lon: -19.9890,
    short: "Ikonisch – besser mit Maßstab und Gegenlicht.",
    long: "Seljalandsfoss – ikonisch, aber immer noch gut, wenn du Menschen als Maßstab nutzt oder ins Gegenlicht gehst.",
    tags: ["klassiker", "wasserfall"]
  },
  { id: "p_gljufrabui", name: "Gljúfrabúi", category: "Wasserfall", lat: 63.6206, lon: -19.9883,
    short: "Versteckter Vorhang – Bühne statt Postkarte.",
    long: "Gljúfrabúi – versteckter Vorhang. Enge, Feuchtigkeit, Gegenlicht: Bühne statt Postkarte.",
    tags: ["klassiker", "wasserfall", "nass"]
  },
  { id: "p_skogafoss", name: "Skógafoss", category: "Wasserfall", lat: 63.5321, lon: -19.5114,
    short: "Kraft und Gischt – auch minimal denkbar.",
    long: "Skógafoss – Kraft und Gischt. Funktioniert klassisch, aber auch minimal, wenn du die Fläche reduzierst.",
    tags: ["klassiker", "wasserfall"]
  },
  { id: "p_kvernufoss", name: "Kvernufoss", category: "Wasserfall", lat: 63.5236, lon: -19.4887,
    short: "Intimer, ruhiger – ideal für klare Lichtkanten.",
    long: "Kvernufoss – kleiner, intimer. Perfekt für ruhige Bilder und klare Lichtkanten.",
    tags: ["wasserfall", "ruhig"]
  },
  { id: "p_solheimajokull", name: "Sólheimajökull", category: "Gletscher", lat: 63.5305, lon: -19.3784,
    short: "Eisstrukturen, Aschelinien – Bewegung im Stillstand.",
    long: "Sólheimajökull – Eisstrukturen, Aschelinien, Bewegung im Stillstand. Nah ran: Textur statt Panorama.",
    tags: ["eis", "textur", "klassiker"]
  },
  { id: "p_dyrholaey", name: "Dyrhólaey", category: "Klippen / Küste", lat: 63.4017, lon: -19.1300,
    short: "Bögen, Kanten, Richtung – Wetter macht das Bild.",
    long: "Dyrhólaey – Bögen, Kanten, Richtung. Wetter macht hier das Bild, nicht die Kamera.",
    tags: ["kuste", "klassiker", "windy"]
  },
  { id: "p_reynisfjara", name: "Reynisfjara", category: "Strand / Basalt", lat: 63.4040, lon: -19.0453,
    short: "Basaltsäulen, Wellen, Rhythmus – stark in SW.",
    long: "Reynisfjara – Basaltsäulen, Wellen, Kontrast. Stark in Schwarzweiß, wenn du Rhythmus betonst.",
    tags: ["klassiker", "basalt", "kuste"]
  },
  { id: "p_vik_church", name: "Vík – Kirche", category: "Ort / Motivanker", lat: 63.4186, lon: -19.0065,
    short: "Ruhiger Fixpunkt über dem Meer.",
    long: "Vík – Kirche als ruhiger Fixpunkt über dem Meer. Ideal als Atemzug zwischen den großen Motiven.",
    tags: ["ort", "ruhig"]
  },
  { id: "p_fjadrargljufur", name: "Fjaðrárgljúfur", category: "Canyon", lat: 63.7717, lon: -18.1723,
    short: "Linien, Kurven, Tiefe – Geduld lohnt.",
    long: "Fjaðrárgljúfur – Linien, Kurven, Tiefe. Geh langsam: der Canyon belohnt Geduld.",
    tags: ["klassiker", "linien"]
  },
  { id: "p_klaustur", name: "Kirkjubæjarklaustur", category: "Ort / Umgebung", lat: 63.7908, lon: -18.0637,
    short: "Orientierungspunkt – Umgebung erzählt die kleinen Geschichten.",
    long: "Kirkjubæjarklaustur – guter Orientierungspunkt. In der Umgebung: Nebel, Weite, kleine Geschichten.",
    tags: ["ort", "weite"]
  },
  { id: "p_svartifoss", name: "Svartifoss", category: "Wasserfall / Basalt", lat: 64.0276, lon: -16.9747,
    short: "Basaltorgeln wie Architektur – Perspektive entscheidet.",
    long: "Svartifoss – Basaltorgeln wie Architektur. Der Klassiker, der sich trotzdem wehren kann: Perspektive entscheidet.",
    tags: ["klassiker", "basalt", "wasserfall"]
  },
  { id: "p_svinafellsjokull", name: "Svínafellsjökull", category: "Gletscherzunge", lat: 64.0116, lon: -16.8608,
    short: "Dramatische Eisfronten – Licht gibt dem Eis Stimme.",
    long: "Svínafellsjökull – dramatische Eisfronten. Licht und Wolken geben dem Eis eine Stimme.",
    tags: ["eis", "dramatisch"]
  },
  { id: "p_jokulsarlon", name: "Jökulsárlón", category: "Lagune", lat: 64.0484, lon: -16.1795,
    short: "Formen statt Wow – Stille fotografieren.",
    long: "Jökulsárlón – Eisberge, Spiegel, Stille. Arbeite mit Formen statt mit „Wow“.",
    tags: ["klassiker", "ruhe", "eis"]
  },
  { id: "p_diamond_beach", name: "Diamond Beach", category: "Strand / Eis", lat: 64.0445, lon: -16.1770,
    short: "Eis auf schwarzem Sand – laut im Ort, leise im Bild.",
    long: "Diamond Beach – Eis auf schwarzem Sand. Der Ort ist laut, das Bild darf leise sein.",
    tags: ["klassiker", "eis", "kuste"]
  },
  { id: "p_stokknes", name: "Stokksnes / Vestrahorn", category: "Dünen / Berge", lat: 64.2491, lon: -14.9713,
    short: "Dünen, Gras, Vestrahorn – Wind & Drama, auch Minimalismus.",
    long: "Stokksnes – Dünen, Gras, Vestrahorn. Ein Ort für Wind und Drama – und für Minimalismus.",
    tags: ["klassiker", "windy", "berge"]
  },
  { id: "p_hofn", name: "Höfn", category: "Ort / Abschluss", lat: 64.2539, lon: -15.2121,
    short: "Hafen, Licht, Alltagsruhe – Satzzeichen am Ende der Route.",
    long: "Höfn – guter Abschluss. Hafen, Licht, Alltagsruhe. Wenn der Tag ausklingt, ist das hier ein Satzzeichen.",
    tags: ["ort", "ruhe"]
  },
];

// ---------- Normalisierung / Validierung ----------
function _spotSafe(s) {
  return String(s).replace(/[&<>"]/g, (c) => ({ "&":"&amp;", "<":"&lt;", ">":"&gt;", '"':"&quot;" }[c]));
}

function _spotFmt(n) {
  return (Math.round(Number(n) * 1e6) / 1e6).toFixed(6);
}

function _normalizeSpot(spot) {
  const out = {
    id: String(spot.id || "").trim(),
    name: String(spot.name || "").trim(),
    category: String(spot.category || "").trim(),
    lat: Number(spot.lat),
    lon: Number(spot.lon),
    short: String(spot.short || "").trim(),
    long: String(spot.long || spot.description || "").trim(),
    tags: Array.isArray(spot.tags) ? spot.tags.map((t) => String(t).trim()).filter(Boolean) : [],
  };
  return out;
}

function _validateSpots(modeKey, spots) {
  const errors = [];
  const ids = new Set();

  for (const s0 of spots) {
    const s = _normalizeSpot(s0);

    if (!s.id) errors.push(`[${modeKey}] Spot ohne id`);
    if (ids.has(s.id)) errors.push(`[${modeKey}] Doppelte id: ${s.id}`);
    ids.add(s.id);

    if (!Number.isFinite(s.lat) || !Number.isFinite(s.lon)) {
      errors.push(`[${modeKey}] Ungültige Koordinaten: ${s.id}`);
      continue;
    }

    if (ENFORCE_ICELAND_ONLY && !isInsideIceland(s.lat, s.lon)) {
      errors.push(`[${modeKey}] Außerhalb Island-Bounds: ${s.id} (${_spotFmt(s.lat)}, ${_spotFmt(s.lon)})`);
    }
  }

  // Fehler bewusst nur loggen – App darf nicht crashen
  if (errors.length) {
    try { console.warn("Spot-Validation:", errors); } catch (_) {}
  }

  // return normalisierte Spots (auch wenn Warnungen)
  return spots.map(_normalizeSpot);
}

// ---------- Darstellung ----------
function _spotPopupHTML(modeKey, spot) {
  const header = modeKey === "drone" ? "Drohnen-Spot" : "Fotografischer Spot";
  const hint =
    modeKey === "drone"
      ? "Hinweis: Inspiration. Keine Flugfreigabe. Ampel/Wind/Regeln separat prüfen."
      : "Hinweis: Orientierung. Kein Drohnenbezug, keine Flugfreigabe.";

  const title = spot.name ? `<div style="font-weight:800; margin-bottom:4px;">${_spotSafe(spot.name)}</div>` : "";
  const cat = spot.category ? `<div style="opacity:.85; margin-bottom:6px;"><i>${_spotSafe(spot.category)}</i></div>` : "";
  const short = spot.short ? `<div style="margin-bottom:8px; opacity:.92; line-height:1.35;">${_spotSafe(spot.short)}</div>` : "";
  const long = spot.long ? `<div style="line-height:1.35;">${_spotSafe(spot.long)}</div>` : "";
  const tags = (spot.tags && spot.tags.length)
    ? `<div style="margin-top:8px; font-size:12px; opacity:.75;">Tags: ${spot.tags.map(_spotSafe).join(", ")}</div>`
    : "";

  return `
    <div style="font-family:system-ui, -apple-system, Segoe UI, Roboto, Arial; max-width:300px">
      <div style="opacity:.65; font-size:12px; font-weight:700; margin-bottom:6px;">${_spotSafe(header)}</div>
      ${title}
      ${cat}
      <div style="margin-bottom:6px; font-size:12px; opacity:.85;">
        Koordinaten: <b>${_spotFmt(spot.lat)}, ${_spotFmt(spot.lon)}</b>
      </div>
      ${short}
      ${long}
      ${tags}
      <div style="margin-top:10px; display:flex; gap:8px; flex-wrap:wrap;">
        <button type="button"
          class="maps-btn"
          data-lat="${spot.lat}"
          data-lon="${spot.lon}"
          data-name=${JSON.stringify(spot.name || "")}
          style="padding:6px 10px; border-radius:10px; border:1px solid rgba(255,255,255,0.14); background:rgba(255,255,255,0.08); color:inherit; cursor:pointer; pointer-events:auto; touch-action:manipulation;">
          In Karten öffnen
        </button>

        <button type="button"
          class="copy-btn"
          data-coords="${_spotFmt(spot.lat)}, ${_spotFmt(spot.lon)}"
          style="padding:6px 10px; border-radius:10px; border:1px solid rgba(255,255,255,0.14); background:rgba(255,255,255,0.06); color:inherit; cursor:pointer; pointer-events:auto; touch-action:manipulation;">
          Koordinaten kopieren
        </button>
      </div>
      <div style="margin-top:10px; font-size:12px; opacity:.7;">${_spotSafe(hint)}</div>
    </div>
  `;
}


async function _jumpToSpot(spot) {
  if (!spot || !Number.isFinite(spot.lat) || !Number.isFinite(spot.lon)) return;

  const g = guardToIceland(spot.lat, spot.lon, "Island-only: Spot liegt außerhalb des erlaubten Bereichs.");
  const lat = g.lat;
  const lon = g.lon;

  try { _setSelectedSpotName(spot.name || ""); } catch (_) {}

  // Pin bewegen + als "manuell" behandeln (kein Routing, keine Navigation)
  try { setMode("manual"); } catch (_) {}
  try { setInputs(lat, lon); } catch (_) {}
  try { updatePills(lat, lon, "Spot"); } catch (_) {}
  try { updateMap(lat, lon, null); } catch (_) {}

  try { manualCoords = { lat, lon }; } catch (_) {}

  try { await runCheckWithCoords(lat, lon, "Spot", null); } catch (_) {}
}

function _buildSpotLayer(modeKey, spots, style) {
  const layer = L.layerGroup();
  for (const s of spots) {
    const m = L.circleMarker([s.lat, s.lon], style);
    m.bindPopup(_spotPopupHTML(modeKey, s));
    m.on("click", () => { _jumpToSpot(s); });
    layer.addLayer(m);
  }
  return layer;
}

// ---------- Runtime state ----------
let _spotMode = SPOT_MODES.drone.key;
let _droneSpotLayer = null;
let _photoSpotLayer = null;

let _DRONE_SPOTS = [];
let _PHOTO_SPOTS = [];

function _ensureSpotLayers() {
  if (!map) return;

  if (!_DRONE_SPOTS.length) _DRONE_SPOTS = _validateSpots("drone", DRONE_SPOTS_RAW);
  if (!_PHOTO_SPOTS.length) _PHOTO_SPOTS = _validateSpots("photo", PHOTO_SPOTS_RAW);

  if (!_droneSpotLayer) {
    _droneSpotLayer = _buildSpotLayer("drone", _DRONE_SPOTS, {
      radius: 7,
      weight: 2,
      opacity: 0.95,
      color: "rgba(88, 24, 124, 0.95)",
      fillColor: "rgba(88, 24, 124, 0.35)",
      fillOpacity: 0.6,
    });
  }

  if (!_photoSpotLayer) {
    _photoSpotLayer = _buildSpotLayer("photo", _PHOTO_SPOTS, {
      radius: 7,
      weight: 2,
      opacity: 0.95,
      color: "rgba(10, 38, 102, 0.95)",
      fillColor: "rgba(10, 38, 102, 0.35)",
      fillOpacity: 0.6,
    });
  }
}

function _setSpotMode(modeKey) {
  const next = modeKey === "photo" ? "photo" : "drone";
  _spotMode = next;

  _ensureSpotLayers();

  // nur EIN Layer sichtbar (klarer Fokus)
  if (map && _droneSpotLayer) {
    const has = map.hasLayer(_droneSpotLayer);
    if (next === "drone" && !has) _droneSpotLayer.addTo(map);
    if (next !== "drone" && has) map.removeLayer(_droneSpotLayer);
  }

  if (map && _photoSpotLayer) {
    const has = map.hasLayer(_photoSpotLayer);
    if (next === "photo" && !has) _photoSpotLayer.addTo(map);
    if (next !== "photo" && has) map.removeLayer(_photoSpotLayer);
  }

  _renderSpotPill();
}

function _renderSpotPill() {
  const pill = document.getElementById("spotPill");
  if (!pill) return;

  const m = SPOT_MODES[_spotMode] || SPOT_MODES.drone;
  pill.textContent = `Spots: ${m.title}`;
}

function _ensureSpotUI() {
  if (document.getElementById("spotBox")) return;

  const box = document.createElement("div");
  box.id = "spotBox";
  box.setAttribute("data-panel-id", "spot");
  box.setAttribute("data-panel-collapsible", "1");
  box.style.marginTop = "10px";
  box.style.padding = "10px";
  box.style.borderRadius = "10px";
  box.style.border = "1px solid rgba(255,255,255,0.08)";
  box.style.background = "rgba(0,0,0,0.25)";
  box.style.color = "inherit";

  box.innerHTML = `
    <div style="display:flex; align-items:center; justify-content:space-between; gap:10px;">
      <div style="font-weight:800;">Spot-Modus</div>
      <div style="display:flex; align-items:center; gap:8px;">
        <div id="spotPill" style="padding:4px 10px; border-radius:999px; font-size:12px; border:1px solid rgba(255,255,255,0.12); opacity:.9;">
        —
      </div>
        <button type="button" data-panel-toggle="spot" aria-label="Spot Panel ein/ausklappen">▾</button>
      </div>
    </div>

    <div data-panel-body>
    <div style="margin-top:8px; display:flex; gap:8px; flex-wrap:wrap;">
      <button id="btnSpotDrone" type="button" style="padding:8px 10px; border-radius:10px; border:1px solid rgba(255,255,255,0.12); background:rgba(255,255,255,0.06); color:inherit; cursor:pointer;">
        ${_spotSafe(SPOT_MODES.drone.title)}
      </button>
      <button id="btnSpotPhoto" type="button" style="padding:8px 10px; border-radius:10px; border:1px solid rgba(255,255,255,0.12); background:rgba(255,255,255,0.06); color:inherit; cursor:pointer;">
        ${_spotSafe(SPOT_MODES.photo.title)}
      </button>
    </div>

    <div id="spotDesc" style="margin-top:8px; opacity:.9; line-height:1.35;">
      —
    </div>

    <div style="margin-top:6px; opacity:.65; font-size:12px; line-height:1.25;">
      Spots sind Inspiration/Orientierung. Keine Navigation, kein Routing, keine Google-Dienste.
    </div>
  </div>
  `;

  if (window.__DA_PANEL__ && window.__DA_PANEL__.register) {
    window.__DA_PANEL__.register(box, "spot", true);
  }

  const anchor = document.getElementById("windBox") || document.getElementById("detail") || document.body;
  anchor.parentNode.insertBefore(box, anchor.nextSibling);

  // Near-Spot-Info (immer sichtbar, aber zeigt nur Inhalt wenn im Radius)
  try {
    if (!document.getElementById("nearSpotBox")) {
      const nb = document.createElement("div");
      nb.id = "nearSpotBox";
      nb.style.marginTop = "10px";
      nb.style.padding = "10px";
      nb.style.borderRadius = "10px";
      nb.style.border = "1px solid rgba(255,255,255,0.08)";
      nb.style.background = "rgba(0,0,0,0.22)";
      nb.style.color = "inherit";

      nb.innerHTML = `
        <div style="font-weight:800;" id="nearSpotTitle">Spot-Info</div>
        <div style="margin-top:4px; opacity:.75; font-size:12px;" id="nearSpotMeta">—</div>
        <div style="margin-top:8px; opacity:.92; line-height:1.35;" id="nearSpotText">—</div>
        <div style="margin-top:8px; opacity:.65; font-size:12px; line-height:1.25;">
          Hinweis: Kontext/Orientierung. Keine Navigation, keine Flugfreigabe.
        </div>
      `;

      // direkt nach Spot-Box einfügen
      if (box && box.parentNode) box.parentNode.insertBefore(nb, box.nextSibling);
    }
  } catch (_) {}

  const bDrone = document.getElementById("btnSpotDrone");
  const bPhoto = document.getElementById("btnSpotPhoto");
  const desc = document.getElementById("spotDesc");

  const paintButtons = () => {
    const on = "rgba(255,255,255,0.12)";
    const off = "rgba(255,255,255,0.06)";
    if (bDrone) bDrone.style.background = (_spotMode === "drone" ? on : off);
    if (bPhoto) bPhoto.style.background = (_spotMode === "photo" ? on : off);

    const m = SPOT_MODES[_spotMode] || SPOT_MODES.drone;
    if (desc) desc.innerHTML = `<b>${_spotSafe(m.title)}</b><br/><span style="opacity:.9">${_spotSafe(m.subtitle)}</span>`;
    _renderSpotPill();
  };

  if (bDrone) bDrone.addEventListener("click", () => { _setSpotMode("drone"); paintButtons(); });
  if (bPhoto) bPhoto.addEventListener("click", () => { _setSpotMode("photo"); paintButtons(); });

  // initial
  paintButtons();
}

function _updateSpotVisibility() {
  if (!map) return;
  _ensureSpotLayers();

  const z = map.getZoom();
  const shouldShow = z >= SPOT_MIN_ZOOM;

  if (!shouldShow) {
    try {
      if (_droneSpotLayer && map.hasLayer(_droneSpotLayer)) map.removeLayer(_droneSpotLayer);
      if (_photoSpotLayer && map.hasLayer(_photoSpotLayer)) map.removeLayer(_photoSpotLayer);
    } catch (_) {}
    return;
  }

  _setSpotMode(_spotMode);
}

// Hook nach Map-Init (robust)
try {
  _ensureSpotUI();
  _updateSpotVisibility();
  map.on("zoomend", _updateSpotVisibility);
} catch (_) {
  const _spotTimer = setInterval(() => {
    try {
      if (typeof map !== "undefined" && map && typeof map.getZoom === "function") {
        _ensureSpotUI();
        _updateSpotVisibility();
        map.on("zoomend", _updateSpotVisibility);
        clearInterval(_spotTimer);
      }
    } catch (_) {}
  }, 250);
}



// =============================
// Spot-Info Hook (Pin → nächster Spot innerhalb 250m)
// =============================
let _spotInfoHooksInstalled = false;

function _spotInfoInstallHooks() {
  if (_spotInfoHooksInstalled) return;
  if (typeof marker === "undefined" || !marker) return;

  // initial render
  try {
    const p = marker.getLatLng();
    _renderNearSpotBox(p.lat, p.lng);
  } catch (_) {}

  const onMove = () => {
    try {
      const p = marker.getLatLng();
      _renderNearSpotBox(p.lat, p.lng);
    } catch (_) {}
  };

  try { marker.on("drag", onMove); } catch (_) {}
  try { marker.on("dragend", onMove); } catch (_) {}

  // updateMap hooken (GPS/Manual/Programmatic)
  try {
    if (typeof updateMap === "function" && !updateMap.__spotInfoWrapped) {
      const _u = updateMap;
      const wrapped = function(lat, lon, accuracyMeters = null) {
        const r = _u(lat, lon, accuracyMeters);
        try { _renderNearSpotBox(lat, lon); } catch (_) {}
        return r;
      };
      wrapped.__spotInfoWrapped = true;
      updateMap = wrapped;
    }
  } catch (_) {}

  _spotInfoHooksInstalled = true;
}

// warten bis marker existiert
const _spotInfoWait = setInterval(() => {
  try {
    if (typeof marker !== "undefined" && marker) {
      _spotInfoInstallHooks();
      clearInterval(_spotInfoWait);
    }
  } catch (_) {}
}, 250);

// =============================
// MAP ACTIONS – Koordinaten-Übergabe (immer verfügbar, unter der Karte)
// - Keine Navigation in der App. Nur Übergabe an Karten-/Navi-App oder Copy.
// - iOS-safe: eigene Buttons im DOM, keine Leaflet-Popup-Abhängigkeit
// =============================
(function installMapHandoffButtons(){
  const BAR_ID = "coordHandoffBar";
  const MSG_ID = "coordHandoffMsg";

  function _fmt6(x){
    const n = Number(x);
    if (!Number.isFinite(n)) return "";
    return (Math.round(n * 1e6) / 1e6).toFixed(6);
  }

  function _getCurrentCoords(){
    // Primär: Marker (Pin)
    try {
      if (typeof marker !== "undefined" && marker && typeof marker.getLatLng === "function") {
        const p = marker.getLatLng();
        if (p && Number.isFinite(p.lat) && Number.isFinite(p.lng)) return { lat: p.lat, lon: p.lng };
      }
    } catch (_) {}

    // Fallback: Inputs
    try {
      if (typeof latInput !== "undefined" && typeof lonInput !== "undefined" && latInput && lonInput) {
        const lat = Number(String(latInput.value || "").trim());
        const lon = Number(String(lonInput.value || "").trim());
        if (Number.isFinite(lat) && Number.isFinite(lon)) return { lat, lon };
      }
    } catch (_) {}

    return null;
  }

  function _ensureBar(){
    if (document.getElementById(BAR_ID)) return;

    const bar = document.createElement("div");
    bar.id = BAR_ID;
    bar.style.display = "flex";
    bar.style.gap = "10px";
    bar.style.flexWrap = "wrap";
    bar.style.alignItems = "center";
    bar.style.margin = "10px 0 8px 0";

    const btnMaps = document.createElement("button");
    btnMaps.type = "button";
    btnMaps.textContent = "In Karten öffnen";
    btnMaps.style.padding = "8px 12px";
    btnMaps.style.borderRadius = "12px";
    btnMaps.style.border = "1px solid rgba(255,255,255,0.14)";
    btnMaps.style.background = "rgba(255,255,255,0.08)";
    btnMaps.style.color = "inherit";
    btnMaps.style.cursor = "pointer";

    const btnCopy = document.createElement("button");
    btnCopy.type = "button";
    btnCopy.textContent = "Koordinaten kopieren";
    btnCopy.style.padding = "8px 12px";
    btnCopy.style.borderRadius = "12px";
    btnCopy.style.border = "1px solid rgba(255,255,255,0.14)";
    btnCopy.style.background = "rgba(255,255,255,0.06)";
    btnCopy.style.color = "inherit";
    btnCopy.style.cursor = "pointer";

    const msg = document.createElement("span");
    msg.id = MSG_ID;
    msg.style.fontSize = "12px";
    msg.style.opacity = "0.75";
    msg.style.marginLeft = "2px";
    msg.textContent = "";

    function _flash(text){
      try {
        msg.textContent = text;
        msg.style.opacity = "0.85";
        window.clearTimeout(msg._t);
        msg._t = window.setTimeout(() => {
          msg.textContent = "";
          msg.style.opacity = "0.75";
        }, 1600);
      } catch (_) {}
    }

    // Click handlers
    let _lastTs = 0;
    function _guardTs(){
      const t = Date.now();
      if (t - _lastTs < 600) return false;
      _lastTs = t;
      return true;
    }

    btnMaps.addEventListener("click", (ev) => {
      ev.preventDefault();
      ev.stopPropagation();
      if (!_guardTs()) return;
      const c = _getCurrentCoords();
      if (!c) return _flash("Keine Koordinaten.");
      try { openInMaps(c.lat, c.lon, ""); } catch (_) {}
    }, { passive: false });

    btnCopy.addEventListener("click", (ev) => {
      ev.preventDefault();
      ev.stopPropagation();
      if (!_guardTs()) return;
      const c = _getCurrentCoords();
      if (!c) return _flash("Keine Koordinaten.");
      const txt = `${_fmt6(c.lat)}, ${_fmt6(c.lon)}`;
      _copyTextToClipboard(txt)
        .then(() => _flash("Kopiert."))
        .catch(() => _flash("Kopieren nicht möglich."));
    }, { passive: false });

    bar.appendChild(btnMaps);
    bar.appendChild(btnCopy);
    bar.appendChild(msg);

    // Insert location: directly above the "Aviation Kontext anzeigen" button if present
    let inserted = false;
    try {
      const buttons = Array.from(document.querySelectorAll("button"));
      const aviBtn = buttons.find(b => (b.textContent || "").trim().toLowerCase().startsWith("aviation kontext"));
      if (aviBtn && aviBtn.parentNode) {
        aviBtn.parentNode.insertBefore(bar, aviBtn);
        inserted = true;
      }
    } catch (_) {}

    if (!inserted) {
      try {
        const mapEl = document.getElementById("map");
        if (mapEl && mapEl.parentNode) {
          // Put directly after map container
          if (mapEl.nextSibling) mapEl.parentNode.insertBefore(bar, mapEl.nextSibling);
          else mapEl.parentNode.appendChild(bar);
          inserted = true;
        }
      } catch (_) {}
    }

    if (!inserted) {
      try { document.body.appendChild(bar); } catch (_) {}
    }
  }

  // Wait for DOM
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", _ensureBar, { once: true });
  } else {
    _ensureBar();
  }
})();
/* ============================================================
   PRE-FLIGHT OVERLAY (additiv, read-only content)
   - Button: "Vor dem ersten Flug"
   - Modal/Overlay mit Regeln & Links
   - Inhalte: JSON-Objekt, UI liest nur
   ============================================================ */

const PREFLIGHT_INFO = {
  title: "Vor dem ersten Flug",
  updated: "2026-01-30",
  intro:
    "Kurz-Check vor dem Start. Diese App ersetzt keine Rechtsberatung. Im Zweifel gelten immer die offiziellen Quellen.",
  sections: [
    {
      id: "easa",
      title: "1) Kategorie & Basisregeln (EASA / Open Category)",
      items: [
        { type: "text", text: "Max. 120 m über Grund/Meer, VLOS (Sichtkontakt), keine riskanten Manöver über Menschenansammlungen." },
        { type: "text", text: "Die Open Category deckt typische Foto-/Reiseflüge ab (Drohnen < 25 kg). Je nach Drohne/Unterkategorie können Online-Test/Kompetenznachweise nötig sein." },
        { type: "link", text: "Offiziell: Drone rules (island.is)", url: "https://island.is/en/drone-rules" },
        { type: "link", text: "Offiziell: Open Category (island.is)", url: "https://island.is/en/open-category" }
      ]
    },
    {
      id: "registration",
      title: "2) Registrierung (Operator-ID)",
      items: [
        { type: "text", text: "Wenn du bereits in einem anderen EASA-Land als Operator registriert bist: nicht doppelt registrieren. Operator-ID am Fluggerät anbringen." },
        { type: "link", text: "Registrierung/Portal: flydrone.is", url: "https://flydrone.is/" }
      ]
    },
    {
      id: "maps",
      title: "3) Kartencheck: Zonen & Schutzgebiete",
      items: [
        { type: "text", text: "Vor Ort prüfen: Aviation-Zonen, temporäre Einschränkungen (Rettung/Events) und Schutzgebiete. Karten sind Orientierung – dein Blick bleibt Pflicht." },
        { type: "link", text: "Iceland Drone Map (island.is)", url: "https://island.is/en/drone-map" },
        { type: "link", text: "UST FAQ: Drones in protected areas", url: "https://ust.is/english/visiting-iceland/faq/" }
      ]
    },
    {
      id: "protected",
      title: "4) Schutzgebiete & Wildlife",
      items: [
        { type: "text", text: "In Schutzgebieten gelten oft Zusatzregeln (auch saisonal). Manche Bereiche sind für Freizeitdrohnen zeitweise komplett tabu." },
        { type: "text", text: "Wenn Tiere reagieren: sofort Höhe/Distanz ändern oder abbrechen. Ruhe ist hier mehr wert als ein Clip." },
        { type: "link", text: "Vatnajökull NP: Drone rules", url: "https://www.vatnajokulsthjodgardur.is/en/thenationalpark/drone-rules" },
        { type: "link", text: "Nattúra: Regeln & Einschränkungen (Übersicht)", url: "https://www.nattura.is/stofnunin/reglur-um-notkun-drona-i-afthreyingarskyni" }
      ]
    },
    {
      id: "insurance",
      title: "5) Versicherung & Verantwortung",
      items: [
        { type: "text", text: "Haftpflicht ist je nach Drohnengewicht/Nutzungsszenario relevant – und in der Praxis immer klug. Für Reisen: Nachweis (englisch) dabei haben." },
        { type: "text", text: "Privatsphäre respektieren: Menschen/Häuser nicht ungefragt filmen. Lieber ein Bild weniger als Ärger mehr." }
      ]
    },
    {
      id: "checklist",
      title: "6) 30-Sekunden-Checkliste",
      items: [
        { type: "text", text: "Wind/Böen ok? (Island: Böen sind der Endgegner). Return-to-Home Höhe sinnvoll? GNSS/Homepoint sitzt?" },
        { type: "text", text: "Start-/Landefläche: keine losen Steine/Grassoden (Propwash), keine Menschen im Rücken." },
        { type: "text", text: "Wenn irgendwas „komisch“ ist: nicht diskutieren – nicht starten." }
      ]
    }
  ]
};

// UI: Button + Modal (minimal-invasiv)
(function () {
  const BTN_ID = "btnPreflight";
  const MODAL_ID = "preflightModal";
  const BACKDROP_ID = "preflightBackdrop";

  function _escape(s) {
    try { return escapeHtml(s); } catch (_) {}
    return String(s)
      .replaceAll("&", "&amp;")
      .replaceAll("<", "&lt;")
      .replaceAll(">", "&gt;")
      .replaceAll('"', "&quot;")
      .replaceAll("'", "&#039;");
  }

  function _buildModalHTML() {
    const info = PREFLIGHT_INFO || {};
    const title = _escape(info.title || "Vor dem ersten Flug");
    const intro = _escape(info.intro || "");
    const updated = _escape(info.updated || "");

    const sections = Array.isArray(info.sections) ? info.sections : [];
    const secHtml = sections.map((sec) => {
      const st = _escape(sec && sec.title ? sec.title : "");
      const items = Array.isArray(sec && sec.items) ? sec.items : [];
      const li = items.map((it) => {
        if (!it) return "";
        if (it.type === "link" && it.url) {
          const text = _escape(it.text || it.url);
          const url = String(it.url);
          return `<li style="margin:6px 0; line-height:1.35;">
            <a href="${_escape(url)}" target="_blank" rel="noopener noreferrer"
               style="color:inherit; text-decoration:underline; text-underline-offset:3px; opacity:.95;">
              ${text}
            </a>
          </li>`;
        }
        const t = _escape(it.text || "");
        return `<li style="margin:6px 0; line-height:1.35; opacity:.95;">${t}</li>`;
      }).join("");

      return `
        <div style="margin-top:14px;">
          <div style="font-weight:800; font-size:14px; margin-bottom:6px;">${st}</div>
          <ul style="margin:0; padding-left:18px; opacity:.95;">
            ${li}
          </ul>
        </div>
      `;
    }).join("");

    return `
      <div id="${MODAL_ID}" role="dialog" aria-modal="true"
           style="position:fixed; inset: 0; z-index: 99999; display:flex; align-items:center; justify-content:center; padding:18px;">
        <div id="${BACKDROP_ID}" style="position:absolute; inset:0; background: rgba(0,0,0,0.62); backdrop-filter: blur(2px);"></div>

        <div style="position:relative; width:min(860px, 92vw); max-height: min(82vh, 720px);
                    overflow:auto; border-radius:16px; border: 1px solid rgba(255,255,255,0.14);
                    background: rgba(20,20,20,0.92); color: inherit; box-shadow: 0 18px 60px rgba(0,0,0,0.45);
                    padding: 14px 14px 16px;">
          <div style="display:flex; align-items:flex-start; justify-content:space-between; gap:12px;">
            <div>
              <div style="font-weight:900; font-size:18px; letter-spacing:.2px;">${title}</div>
              <div style="margin-top:4px; opacity:.8; line-height:1.35; font-size:13px;">${intro}</div>
              ${updated ? `<div style="margin-top:6px; opacity:.55; font-size:12px;">Stand: ${updated}</div>` : ""}
            </div>

            <button type="button" id="preflightClose"
              style="flex:0 0 auto; padding:8px 10px; border-radius:12px; border:1px solid rgba(255,255,255,0.16);
                     background: rgba(255,255,255,0.08); color: inherit; cursor:pointer;">
              Schließen ✕
            </button>
          </div>

          ${secHtml}

          <div style="margin-top:14px; opacity:.65; font-size:12px; line-height:1.35;">
            Hinweis: Regeln können sich ändern, lokal/temporär abweichen (Rettung, Events, Wildlife). Im Zweifel: nicht fliegen.
          </div>
        </div>
      </div>
    `;
  }

  function _openModal() {
    try {
      if (document.getElementById(MODAL_ID)) return;

      // lock scroll behind
      try {
        const b = document.body;
        if (b) {
          b.dataset._preflightOverflow = b.style.overflow || "";
          b.style.overflow = "hidden";
        }
      } catch (_) {}

      const wrap = document.createElement("div");
      wrap.innerHTML = _buildModalHTML();
      const modal = wrap.firstElementChild;
      if (!modal) return;
      document.body.appendChild(modal);

      const closeBtn = document.getElementById("preflightClose");
      const backdrop = document.getElementById(BACKDROP_ID);

      function _close() {
        try {
          const m = document.getElementById(MODAL_ID);
          if (m && m.parentNode) m.parentNode.removeChild(m);
        } catch (_) {}

        try {
          const b = document.body;
          if (b) b.style.overflow = (b.dataset._preflightOverflow || "");
          if (b) delete b.dataset._preflightOverflow;
        } catch (_) {}

        try { document.removeEventListener("keydown", _onKey, true); } catch (_) {}
      }

      function _onKey(ev) {
        try {
          if (!ev) return;
          const k = ev.key || ev.code || "";
          if (k === "Escape" || k === "Esc") {
            ev.preventDefault();
            _close();
          }
        } catch (_) {}
      }

      if (closeBtn) closeBtn.addEventListener("click", (e) => { try { e.preventDefault(); } catch (_) {} _close(); }, { passive: false });
      if (backdrop) backdrop.addEventListener("click", (e) => { try { e.preventDefault(); } catch (_) {} _close(); }, { passive: false });

      document.addEventListener("keydown", _onKey, true);
    } catch (_) {}
  }

  function _ensureButton() {
    try {
      if (document.getElementById(BTN_ID)) return;

      const btn = document.createElement("button");
      btn.id = BTN_ID;
      btn.type = "button";
      btn.textContent = (PREFLIGHT_INFO && PREFLIGHT_INFO.title) ? PREFLIGHT_INFO.title : "Vor dem ersten Flug";
      btn.style.padding = "8px 12px";
      btn.style.borderRadius = "12px";
      btn.style.border = "1px solid rgba(255,255,255,0.14)";
      btn.style.background = "rgba(255,255,255,0.06)";
      btn.style.color = "inherit";
      btn.style.cursor = "pointer";
      btn.style.pointerEvents = "auto";
      btn.style.touchAction = "manipulation";

      btn.addEventListener("click", (ev) => {
        try { ev.preventDefault(); ev.stopPropagation(); } catch (_) {}
        _openModal();
      }, { passive: false });

      // Insert location: above the first "Aviation Kontext ..." button, else after map, else after windBox/detail.
      let inserted = false;

      try {
        const buttons = Array.from(document.querySelectorAll("button"));
        const aviBtn = buttons.find(b => (b.textContent || "").trim().toLowerCase().startsWith("aviation kontext"));
        if (aviBtn && aviBtn.parentNode) {
          aviBtn.parentNode.insertBefore(btn, aviBtn);
          inserted = true;
        }
      } catch (_) {}

      if (!inserted) {
        try {
          const mapEl = document.getElementById("map");
          if (mapEl && mapEl.parentNode) {
            if (mapEl.nextSibling) mapEl.parentNode.insertBefore(btn, mapEl.nextSibling);
            else mapEl.parentNode.appendChild(btn);
            inserted = true;
          }
        } catch (_) {}
      }

      if (!inserted) {
        try {
          const anchor = document.getElementById("windBox") || document.getElementById("detail") || document.body;
          if (anchor && anchor.parentNode) {
            anchor.parentNode.insertBefore(btn, anchor.nextSibling);
            inserted = true;
          }
        } catch (_) {}
      }

      if (!inserted) {
        try { document.body.appendChild(btn); } catch (_) {}
      }
    } catch (_) {}
  }

  // UI is built dynamically by the app; wait a moment and retry a few times.
  (function _deferEnsure() {
    let tries = 0;
    const maxTries = 20; // ~10s total (500ms steps)
    const tick = () => {
      tries += 1;
      _ensureButton();
      if (document.getElementById(BTN_ID)) return; // inserted successfully
      if (tries >= maxTries) return;
      setTimeout(tick, 500);
    };
    setTimeout(tick, 800);
  })();
})();
// =============================
// SUN / Tageslicht + Wetter-Zeitleiste (Open-Meteo) – additiv, minimal-invasiv
// Ziel: Von Sonnenaufgang bis Sonnenuntergang eine stündliche Vorschau am Standort.
// - Sonnenzeiten: lokal im Browser berechnet (keine externen Dienste nötig)
// - Wetter (Icons): Open-Meteo hourly (frei), nur Anzeige, ohne Speicherung/Tracking
// - UI: Box unter IMO-Box
// =============================

const SUN_TZ = "Atlantic/Reykjavik";
const SUN_API_BASE = "https://api.open-meteo.com/v1/forecast";
const SUN_THROTTLE_MS = 60_000;

let sunHooksInstalled = false;
let sunLastFetchAt = 0;
let sunLastKey = "";
let sunLastPayloadKey = "";
let sunLastPayload = null;

// Auto-Play (Slider folgt Uhr, pausiert bei User-Interaktion)
let sunAutoTimer = null;
let sunLastUserInteractAt = 0;
let sunAutoLastIdx = -1;

// --- Mini-Utils (leise) ---
function sunClamp(n, a, b) { return Math.max(a, Math.min(b, n)); }
function sunPad2(n) { return String(n).padStart(2, "0"); }

function sunParseISOToUTC(iso) {
  try {
    if (!iso || typeof iso !== "string") return new Date(NaN);
    const m = iso.match(/^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2})/);
    if (!m) return new Date(iso);
    const y = Number(m[1]), mo = Number(m[2]), d = Number(m[3]), hh = Number(m[4]), mm = Number(m[5]);
    return new Date(Date.UTC(y, mo - 1, d, hh, mm, 0));
  } catch (_) {
    return new Date(iso);
  }
}

function sunFmtHHMM(date, tz = SUN_TZ) {
  try {
    const fmt = new Intl.DateTimeFormat("de-DE", { timeZone: tz, hour: "2-digit", minute: "2-digit", hour12: false });
    return fmt.format(date);
  } catch (_) {
    // Fallback: lokale Zeit
    return `${sunPad2(date.getHours())}:${sunPad2(date.getMinutes())}`;
  }
}

function sunNowInTz(tz = SUN_TZ) {
  try {
    // "jetzt" als Datum, aber Tages-Komponenten in Ziel-TZ
    const parts = new Intl.DateTimeFormat("en-CA", { timeZone: tz, year: "numeric", month: "2-digit", day: "2-digit" })
      .formatToParts(new Date())
      .reduce((a, p) => (a[p.type] = p.value, a), {});
    const y = Number(parts.year), m = Number(parts.month), d = Number(parts.day);
    // Mitternacht in UTC für diesen TZ-Tag (wir rechnen später in UTC weiter)
    return { y, m, d };
  } catch (_) {
    const n = new Date();
    return { y: n.getFullYear(), m: n.getMonth() + 1, d: n.getDate() };
  }
}

// --- Sonnenzeiten (NOAA-Algorithmus, ausreichend genau für Planung) ---
function sunToRad(deg) { return (deg * Math.PI) / 180; }
function sunToDeg(rad) { return (rad * 180) / Math.PI; }

function sunCalcSunTimesUTC(lat, lon, y, m, d) {
  // returns { sunrise: Date, sunset: Date } in UTC
  // Algorithmus: NOAA Solar Calculator (vereinfachte Variante)
  // https://gml.noaa.gov/grad/solcalc/ (Konzept), implementiert ohne externe Lib.
  const J1970 = 2440588;
  const J2000 = 2451545;

  function toJulian(dateMs) { return dateMs / 86400000 - 0.5 + J1970; }
  function fromJulian(j) { return new Date((j + 0.5 - J1970) * 86400000); }
  function toDays(j) { return j - J2000; }

  function rightAscension(l, b) {
    const e = sunToRad(23.4397);
    return Math.atan2(Math.sin(l) * Math.cos(e) - Math.tan(b) * Math.sin(e), Math.cos(l));
  }
  function declination(l, b) {
    const e = sunToRad(23.4397);
    return Math.asin(Math.sin(b) * Math.cos(e) + Math.cos(b) * Math.sin(e) * Math.sin(l));
  }
  function solarMeanAnomaly(d) { return sunToRad(357.5291 + 0.98560028 * d); }
  function eclipticLongitude(M) {
    const C = sunToRad(1.9148) * Math.sin(M) + sunToRad(0.02) * Math.sin(2 * M) + sunToRad(0.0003) * Math.sin(3 * M);
    const P = sunToRad(102.9372);
    return M + C + P + Math.PI;
  }
  function siderealTime(d, lw) { return sunToRad(280.16 + 360.9856235 * d) - lw; }
  function julianCycle(d, lw) { return Math.round(d - 0.0009 - lw / (2 * Math.PI)); }
  function approxTransit(Ht, lw, n) { return 0.0009 + (Ht + lw) / (2 * Math.PI) + n; }
  function solarTransitJ(ds, M, L) { return J2000 + ds + 0.0053 * Math.sin(M) - 0.0069 * Math.sin(2 * L); }
  function hourAngle(h, phi, dec) {
    return Math.acos((Math.sin(h) - Math.sin(phi) * Math.sin(dec)) / (Math.cos(phi) * Math.cos(dec)));
  }
  function getSetJ(h, lw, phi, dec, n, M, L, isSunrise) {
    const w = hourAngle(h, phi, dec);
    const a = approxTransit(isSunrise ? -w : w, lw, n);
    return solarTransitJ(a, M, L);
  }

  const lw = sunToRad(-lon);
  const phi = sunToRad(lat);

  // Datum (UTC) – wir berechnen für den Tag in Ziel-TZ: y/m/d
  const dateUTC = Date.UTC(y, m - 1, d, 12, 0, 0); // Mittags-Anker in UTC
  const d0 = toDays(toJulian(dateUTC));

  const n = julianCycle(d0, lw);
  const ds = approxTransit(0, lw, n);

  const M = solarMeanAnomaly(ds);
  const L = eclipticLongitude(M);

  const dec = declination(L, 0);

  // Sonnenauf/-untergang: h0 = -0.833° (Atmosphäre + Sonnenradius)
  const h0 = sunToRad(-0.833);

  const Jset = getSetJ(h0, lw, phi, dec, n, M, L, false);
  const Jrise = getSetJ(h0, lw, phi, dec, n, M, L, true);

  return { sunrise: fromJulian(Jrise), sunset: fromJulian(Jset) };
}

// Sonnenhöhe (Altitude) in Grad, UTC-Date object
function sunCalcAltitudeDegUTC(lat, lon, dateUTC) {
  try {
    // basiert auf denselben Grundformeln wie sunCalcSunTimesUTC (minimal extrahiert)
    const rad = Math.PI / 180;
    const lw = -lon * rad;
    const phi = lat * rad;
    const d = (Date.UTC(dateUTC.getUTCFullYear(), dateUTC.getUTCMonth(), dateUTC.getUTCDate(), dateUTC.getUTCHours(), dateUTC.getUTCMinutes(), dateUTC.getUTCSeconds()) / 86400000) - (Date.UTC(2000,0,1,12,0,0) / 86400000);
    const M = (357.5291 + 0.98560028 * d) * rad;
    const C = (1.9148 * Math.sin(M) + 0.02 * Math.sin(2*M) + 0.0003 * Math.sin(3*M)) * rad;
    const P = 102.9372 * rad;
    const L = M + C + P + Math.PI;
    const e = 23.4397 * rad;
    const dec = Math.asin(Math.sin(e) * Math.sin(L));
    const ra = Math.atan2(Math.sin(L) * Math.cos(e), Math.cos(L));
    const st = (280.16 + 360.9856235 * d) * rad - lw;
    const H = st - ra;
    const alt = Math.asin(Math.sin(phi) * Math.sin(dec) + Math.cos(phi) * Math.cos(dec) * Math.cos(H));
    return alt / rad;
  } catch (_) { return NaN; }
}

function sunPhotoScore(t, tSunrise, tSunset) {
  // Returns 0..1 (minimalistic heuristic):
  // Blue hour: [-2h..-1h] and [+1h..+2h] -> 0.45
  // Golden hour: [-1h..0] and [0..+1h] around sunrise/sunset -> 0.85
  // Daytime -> 0.25 (flatter, "harsher light")
  // Night -> 0
  try {
    const twoH = 2 * 60 * 60 * 1000;
    const oneH = 1 * 60 * 60 * 1000;

    if (!Number.isFinite(t) || !Number.isFinite(tSunrise) || !Number.isFinite(tSunset)) return 0;

    if (t < tSunrise - twoH) return 0;
    if (t >= tSunrise - twoH && t < tSunrise - oneH) return 0.45; // blue pre
    if (t >= tSunrise - oneH && t < tSunrise + oneH) return 0.85; // golden around sunrise
    if (t > tSunrise + oneH && t < tSunset - oneH) return 0.25; // daytime
    if (t >= tSunset - oneH && t <= tSunset + oneH) return 0.85; // golden around sunset
    if (t > tSunset + oneH && t <= tSunset + twoH) return 0.45; // blue post
    return 0;
  } catch (_) { return 0; }
}

function sunDrawCurve(payload, selectedIdx) {
  try {
    const c = document.getElementById("sunCurve");
    if (!c || !c.getContext) return;
    const ctx = c.getContext("2d");
    if (!ctx) return;

    const { sunriseUTC, sunsetUTC, tz, hours } = payload || {};
    if (!(sunriseUTC instanceof Date) || !(sunsetUTC instanceof Date)) return;

    const w = c.width || 680;
    const h = c.height || 90;
    ctx.clearRect(0, 0, w, h);

    // Plot area with simple axes
    const padL = 26;
    const padR = 10;
    const padT = 10;
    const padB = 18;
    const x0 = padL;
    const y0 = h - padB;
    const x1 = w - padR;
    const y1 = padT;

    // Time window (Mode: photo / 24h)
    const tSunrise = sunriseUTC.getTime();
    const tSunset = sunsetUTC.getTime();

    const mode = (typeof window !== "undefined" && window.__DA_SUN_MODE__ === "24h") ? "24h" : "photo";
    let tStart, tEnd;

    // main sun curve does not use axis overrides
    const hasAxis = false;

    if (!hasAxis && mode === "24h") {
      const y = sunriseUTC.getUTCFullYear();
      const mo = sunriseUTC.getUTCMonth();
      const da = sunriseUTC.getUTCDate();
      tStart = Date.UTC(y, mo, da, 0, 0, 0);
      tEnd = tStart + 24 * 60 * 60 * 1000;
    } else if (!hasAxis) {
      const extra = 2 * 60 * 60 * 1000;
      tStart = tSunrise - extra;
      tEnd = tSunset + extra;
    }

    const span = Math.max(1, tEnd - tStart);

    const toX = (t) => x0 + ((t - tStart) / span) * (x1 - x0);

    // axes
    ctx.globalAlpha = 0.9;
    ctx.lineWidth = 1;
    ctx.strokeStyle = "rgba(255,255,255,0.25)";
    // y-axis
    ctx.beginPath(); ctx.moveTo(x0, y1); ctx.lineTo(x0, y0); ctx.stroke();
    // x-axis
    ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); ctx.stroke();

    // Background zones (ruhig, aber sichtbar): Nacht/Blue/Golden/Day (relativ zu Sunrise/Sunset)
    try {
      const xSr = toX(tSunrise);
      const xSs = toX(tSunset);

      const hour = 60 * 60 * 1000;
      const xStart = toX(tStart);
      const xEnd = toX(tEnd);

      const xBlueStartM = toX(tSunrise - hour);
      const xGoldenEndM = toX(tSunrise + hour);

      const xGoldenStartE = toX(tSunset - hour);
      const xBlueEndE = toX(tSunset + hour);

      // Nacht (vor Blue Hour morgens) – sehr dezent, eher als „Dämpfung“
      ctx.globalAlpha = 0.18;
      ctx.fillStyle = "rgba(0,0,0,0.22)";
      ctx.fillRect(xStart, y1, Math.max(0, Math.min(xBlueStartM, xEnd) - xStart), (y0 - y1));

      // Blue Hour vor Sunrise (kühles Blau)
      ctx.globalAlpha = 0.30;
      ctx.fillStyle = "rgba(70,130,255,0.30)";
      ctx.fillRect(Math.max(xBlueStartM, xStart), y1, Math.max(0, Math.min(xSr, xEnd) - Math.max(xBlueStartM, xStart)), (y0 - y1));

      // Golden Hour nach Sunrise (warm, dezent)
      ctx.globalAlpha = 0.22;
      ctx.fillStyle = "rgba(255,200,90,0.22)";
      ctx.fillRect(Math.max(xSr, xStart), y1, Math.max(0, Math.min(xGoldenEndM, xEnd) - Math.max(xSr, xStart)), (y0 - y1));

      // Tageslicht (neutral – sehr dezent)
      ctx.globalAlpha = 0.10;
      ctx.fillStyle = "rgba(255,255,255,0.10)";
      ctx.fillRect(Math.max(xGoldenEndM, xStart), y1, Math.max(0, Math.min(xGoldenStartE, xEnd) - Math.max(xGoldenEndM, xStart)), (y0 - y1));

      // Golden Hour vor Sunset
      ctx.globalAlpha = 0.22;
      ctx.fillStyle = "rgba(255,200,90,0.22)";
      ctx.fillRect(Math.max(xGoldenStartE, xStart), y1, Math.max(0, Math.min(xSs, xEnd) - Math.max(xGoldenStartE, xStart)), (y0 - y1));

      // Blue Hour nach Sunset (kühles Blau)
      ctx.globalAlpha = 0.30;
      ctx.fillStyle = "rgba(70,130,255,0.30)";
      ctx.fillRect(Math.max(xSs, xStart), y1, Math.max(0, Math.min(xBlueEndE, xEnd) - Math.max(xSs, xStart)), (y0 - y1));

      // Nacht (nach Blue Hour abends) – sehr dezent
      ctx.globalAlpha = 0.18;
      ctx.fillStyle = "rgba(0,0,0,0.22)";
      ctx.fillRect(Math.max(xBlueEndE, xStart), y1, Math.max(0, xEnd - Math.max(xBlueEndE, xStart)), (y0 - y1));

      // Sunrise / Sunset markers (hell, aber ruhig)
      ctx.globalAlpha = 0.70;
      ctx.lineWidth = 1;
      ctx.strokeStyle = "rgba(255,255,255,0.35)";
      ctx.beginPath(); ctx.moveTo(xSr, y1); ctx.lineTo(xSr, y0); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(xSs, y1); ctx.lineTo(xSs, y0); ctx.stroke();

      // Labels (minimal): -2h | Sunrise | Sunset | +2h
      ctx.globalAlpha = 0.75;
      ctx.fillStyle = "rgba(255,255,255,0.70)";
      ctx.font = "10px system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial";
      ctx.textBaseline = "bottom";

      const clampX = (x) => Math.max(x0 + 2, Math.min(x1 - 2, x));
      ctx.textAlign = "left";
      if (mode === "24h") {
        ctx.fillText("00:00", clampX(xStart + 2), y0 - 2);
      } else {
        ctx.fillText("-2h", clampX(xStart + 2), y0 - 2);
      }

      ctx.textAlign = "center";
      ctx.fillText("Sunrise", clampX(xSr), y0 - 2);
      ctx.fillText("Sunset", clampX(xSs), y0 - 2);

      ctx.textAlign = "right";
      if (mode === "24h") {
        ctx.fillText("24:00", clampX(xEnd - 2), y0 - 2);
      } else {
        ctx.fillText("+2h", clampX(xEnd - 2), y0 - 2);
      }
    } catch (_) {}


    // sample curve (every 10 minutes, max ~110 points for extended span)
    const stepMs = Math.max(10 * 60 * 1000, Math.floor(span / 110));
    const pts = [];
    for (let t = tStart; t <= tEnd; t += stepMs) {
      const alt = sunCalcAltitudeDegUTC(payload.lat, payload.lon, new Date(t));
      if (Number.isFinite(alt)) pts.push({ t, alt });
    }
    if (pts.length < 2) return;

    // normalize altitude for display (twilight-aware)
    // Wir „klemmen“ die Kurve bei -6° (civil twilight) auf 0,
    // damit die ersten Stunden wirklich am Nullpunkt bleiben.
    const twilightAlt = -6; // degrees
    let maxAlt = -Infinity;
    for (const p of pts) { if (p.alt > maxAlt) maxAlt = p.alt; }
    if (!Number.isFinite(maxAlt) || maxAlt - twilightAlt < 1e-6) return;
    const denom = maxAlt - twilightAlt;

    const toY = (alt) => {
      const nRaw = (alt - twilightAlt) / denom;
      const n = Math.max(0, Math.min(1, nRaw));
      const yy = y0 - n * (y0 - y1);
      return Math.max(y1, Math.min(y0, yy));
    };

    // draw curve (yellow)
    ctx.globalAlpha = 0.95;
    ctx.lineWidth = 2;
    ctx.strokeStyle = "rgba(255,212,0,0.90)";
    ctx.beginPath();
    ctx.moveTo(toX(pts[0].t), toY(pts[0].alt));
    for (let i = 1; i < pts.length; i++) ctx.lineTo(toX(pts[i].t), toY(pts[i].alt));
    ctx.stroke();

    // secondary curve (photo window heuristic) – subtle line above the yellow curve
    try {
      ctx.globalAlpha = 0.55;
      ctx.lineWidth = 1.4;
      ctx.strokeStyle = "rgba(255,255,255,0.45)";
      ctx.beginPath();
      const liftMax = 10; // px
      const yLift = (t) => {
        const s = sunPhotoScore(t, tSunrise, tSunset);
        return (Number.isFinite(s) ? s : 0) * liftMax;
      };
      ctx.moveTo(toX(pts[0].t), Math.max(y1, Math.min(y0, toY(pts[0].alt) - yLift(pts[0].t))));
      for (let i = 1; i < pts.length; i++) {
        const xx = toX(pts[i].t);
        const yy = Math.max(y1, Math.min(y0, toY(pts[i].alt) - yLift(pts[i].t)));
        ctx.lineTo(xx, yy);
      }
      ctx.stroke();
    } catch (_) {}

    // selected marker (from slider) – Index ODER Zeitstempel in ms
    let selTime = null;
    try {
      if (Number(selectedIdx) > 1e12) {
        selTime = Number(selectedIdx);
      } else {
        const i = sunClamp(Number(selectedIdx) || 0, 0, (hours?.length || 1) - 1);
        selTime = Date.parse(hours[i]?.time || "") || null;
      }
    } catch (_) {}
    if (selTime) {
      const x = toX(selTime);
      // vertical line
      ctx.globalAlpha = 0.8;
      ctx.lineWidth = 1;
      ctx.strokeStyle = "rgba(255,212,0,0.55)";
      ctx.beginPath(); ctx.moveTo(x, y1); ctx.lineTo(x, y0); ctx.stroke();
      // dot on curve
      const altNow = sunCalcAltitudeDegUTC(payload.lat, payload.lon, new Date(selTime));
      const y = Number.isFinite(altNow) ? toY(altNow) : y0;
      ctx.fillStyle = "rgba(255,212,0,0.98)";
      ctx.beginPath(); ctx.arc(x, y, 3, 0, Math.PI * 2); ctx.fill();
      try {
        const phase = (Date.now() % 1000) / 1000;
        const r = 6 + 3 * Math.sin(phase * Math.PI * 2);
        ctx.strokeStyle = "rgba(255,215,0,0.55)";
        ctx.lineWidth = 2;
        ctx.beginPath(); ctx.arc(x, y, Math.max(2, r), 0, Math.PI * 2); ctx.stroke();
      } catch (_) {}
    }

    
    
    
    // now marker (realtime) – DISTANZ-LESBAR + subtiler Pulse (4.8s) für schnellen Fokus
    try {
      const nowT = Date.now(); // Island = UTC
      if (Number.isFinite(nowT) && nowT >= tStart && nowT <= tEnd) {
        const xN = toX(nowT);

        // Pulse: sehr langsam, sehr klein – eher "Atmen" als Blinken
        const phase = (nowT % 4800) / 4800;
        const pulse = 0.5 + 0.5 * Math.sin(phase * Math.PI * 2); // 0..1
        const pA = 0.85 + 0.15 * pulse; // 0.85..1.0
        const pW = 0.90 + 0.20 * pulse; // 0.90..1.10

        // Core Linie – bleibt kontrolliert (nicht zu fett)
        ctx.globalAlpha = 1;
        ctx.lineWidth = 2.6;
        ctx.strokeStyle = "rgba(255,215,0,1)";
        ctx.beginPath(); ctx.moveTo(xN, y1); ctx.lineTo(xN, y0); ctx.stroke();

        // Glow Layer 1 – nah, klar sichtbar
        ctx.globalAlpha = 0.55 * pA;
        ctx.lineWidth = 6 * pW;
        ctx.strokeStyle = "rgba(255,215,0,0.75)";
        ctx.beginPath(); ctx.moveTo(xN, y1); ctx.lineTo(xN, y0); ctx.stroke();

        // Glow Layer 2 – weich, Eye Catch aus Distanz
        ctx.globalAlpha = 0.25 * pA;
        ctx.lineWidth = 12 * pW;
        ctx.strokeStyle = "rgba(255,215,0,0.45)";
        ctx.beginPath(); ctx.moveTo(xN, y1); ctx.lineTo(xN, y0); ctx.stroke();

        // Glow Layer 3 – ultra soft Atmosphere
        ctx.globalAlpha = 0.12 * pA;
        ctx.lineWidth = 20 * pW;
        ctx.strokeStyle = "rgba(255,215,0,0.25)";
        ctx.beginPath(); ctx.moveTo(xN, y1); ctx.lineTo(xN, y0); ctx.stroke();

        // Punkt – sichtbar auf kleiner Mobile Fläche
        const altN = sunCalcAltitudeDegUTC(payload.lat, payload.lon, new Date(nowT));
        const yN = Number.isFinite(altN) ? toY(altN) : y0;

        ctx.globalAlpha = 1;
        ctx.fillStyle = "rgba(255,215,0,1)";
        ctx.beginPath(); ctx.arc(xN, yN, 3.8, 0, Math.PI * 2); ctx.fill();

        // Punkt Halo Layer 1
        ctx.globalAlpha = 0.55 * pA;
        ctx.fillStyle = "rgba(255,215,0,0.85)";
        ctx.beginPath(); ctx.arc(xN, yN, 6.5 * pW, 0, Math.PI * 2); ctx.fill();

        // Punkt Halo Layer 2
        ctx.globalAlpha = 0.25 * pA;
        ctx.fillStyle = "rgba(255,215,0,0.6)";
        ctx.beginPath(); ctx.arc(xN, yN, 10 * pW, 0, Math.PI * 2); ctx.fill();
      }
    } catch (_) {}


    // selection marker overlay (Slider-Auswahl) – bewusst anders als NOW-Marker
    try {
      let tSel = NaN;
      if (Number(selectedIdx) > 1e12) {
        tSel = Number(selectedIdx);
      } else if (hours && hours.length) {
        const iSel = sunClamp(Number(selectedIdx) || 0, 0, (hours.length || 1) - 1);
        tSel = Date.parse(hours[iSel]?.time || "") || NaN;
      }

      if (Number.isFinite(tSel)) {
        const xSel = toX(tSel);

        // thin neutral line (white-ish) so user can distinguish selection vs NOW
        ctx.globalAlpha = 0.55;
        ctx.lineWidth = 2;
        ctx.strokeStyle = "rgba(255,255,255,0.35)";
        ctx.beginPath(); ctx.moveTo(xSel, y1); ctx.lineTo(xSel, y0); ctx.stroke();

        // small dot at curve (white)
        const altSel = sunCalcAltitudeDegUTC(payload.lat, payload.lon, new Date(tSel));
        const ySel = Number.isFinite(altSel) ? toY(altSel) : y0;
        ctx.globalAlpha = 0.9;
        ctx.fillStyle = "rgba(255,255,255,0.85)";
        ctx.beginPath(); ctx.arc(xSel, ySel, 2.8, 0, Math.PI * 2); ctx.fill();
      }
    } catch (_) {}





    // y label minimal
    ctx.globalAlpha = 0.6;
    ctx.fillStyle = "rgba(255,212,0,0.70)";
    ctx.font = "12px system-ui, -apple-system, Segoe UI, Roboto, Arial";
    ctx.fillText("☀", 6, y1 + 12);
  } catch (_) {}
}


// --- UI ---
function sunEnsureUI() {
  if (document.getElementById("sunBox")) return;

  const imo = document.getElementById("imoBox");
  const anchor = imo || document.getElementById("windBox") || document.getElementById("detail") || document.getElementById("state") || document.body;
  if (!anchor || !anchor.parentNode) return;

  const box = document.createElement("div");
  box.id = "sunBox";
  box.setAttribute("data-panel-id", "sun");
  box.setAttribute("data-panel-collapsible", "1");
  box.style.marginTop = "10px";
  box.style.padding = "10px";
  box.style.borderRadius = "10px";
  box.style.border = "1px solid rgba(255,255,255,0.08)";
  box.style.background = "rgba(0,0,0,0.25)";
  box.style.color = "inherit";

  box.innerHTML = `
    <div style="display:flex; align-items:center; justify-content:space-between; gap:10px;">
      <div style="font-weight:700;">Licht & Wetter (Sunrise → Sunset)</div>
      <div style="display:flex; align-items:center; gap:8px;">
        <div style="opacity:.65; font-size:12px;">Data: Open-Meteo</div>
        <button type="button" id="sunModeToggle" data-sun-mode-toggle="1" aria-label="Zeitachse umschalten" style="border:1px solid rgba(255,255,255,.15); background:rgba(255,255,255,.06); color:inherit; border-radius:999px; padding:4px 10px; font-size:12px; cursor:pointer;">Foto</button>
        <button type="button" data-panel-toggle="sun" aria-label="Licht Panel ein/ausklappen">▾</button>
      </div>
    </div>

    <div data-panel-body>

    <div id="sunMeta" style="margin-top:6px; opacity:.9; font-size:13px; line-height:1.35;">—</div>

    <canvas id="sunCurve" width="680" height="90" style="width:100%; height:90px; margin-top:8px; display:block; border-radius:8px; background:rgba(255,255,255,0.03);"></canvas>
    <div id="sunAxisLabel" style="display:flex; justify-content:space-between; margin-top:4px; font-size:12px; opacity:.75;">
      <span>Aufgang</span><span>Untergang</span>
    </div>


    <div id="sunTimeline" style="margin-top:8px;">
      <input id="sunSlider" type="range" min="0" max="10" value="0" step="1" style="width:100%;"/>
      <div id="sunTicks" style="display:flex; justify-content:space-between; gap:6px; margin-top:6px; font-size:12px; opacity:.95;"></div>
      <div id="sunHint" style="margin-top:6px; opacity:.65; font-size:12px; line-height:1.25;">
        Stündliche Vorschau. Keine Garantie – Wetter bleibt Wetter.
      </div>
    </div>

    <div style="margin-top:10px; border-top:1px solid rgba(255,255,255,0.07);"></div>

    <div id="sunPlanTrigger" role="button" tabindex="0" aria-expanded="false"
      style="margin-top:8px; display:flex; align-items:center; justify-content:space-between; gap:10px; cursor:pointer; user-select:none;">
      <div style="font-size:12px; opacity:.9;">Planung öffnen — +48h</div>
      <div id="sunPlanChevron" aria-hidden="true" style="font-size:12px; opacity:.7; transform:rotate(0deg); transition:transform 220ms ease;">▸</div>
    </div>

    <div id="sunPlanBody"
      style="margin-top:8px; overflow:hidden; max-height:0px; opacity:0; transition:max-height 320ms ease, opacity 320ms ease;">
      <div style="padding:10px; border-radius:10px; border:1px solid rgba(255,255,255,0.08); background:rgba(255,255,255,0.03);">
        <div style="display:flex; align-items:center; justify-content:space-between; gap:10px;">
          <div style="font-size:12px; opacity:.9;">Vorschau — +48h</div>
          <div style="font-size:12px; opacity:.65;">(gleiche Logik, Zeit versetzt)</div>
        </div>

        <div style="margin-top:8px; border-radius:12px; border:1px solid rgba(255,255,255,0.06); background:rgba(0,0,0,0.22); padding:8px;">
          <canvas id="sunPlanCurve" width="680" height="90" style="width:100%; height:90px; display:block;"></canvas>
          <div id="sunPlanAxis" style="display:flex; justify-content:space-between; margin-top:6px; font-size:12px; opacity:.85;">
            <span>—</span><span>—</span>
          </div>
        </div>

        <div id="sunPlanTimeline" style="margin-top:8px;">
          <input id="sunPlanSlider" type="range" min="0" max="10" value="0" step="1" style="width:100%;"/>
          <div id="sunPlanTicks" style="display:flex; justify-content:space-between; gap:6px; margin-top:6px; font-size:12px; opacity:.95;"></div>
          <div id="sunPlanHint" style="margin-top:6px; opacity:.65; font-size:12px; line-height:1.25;">
            Vorschau +48h. Keine Garantie – Wetter bleibt Wetter.
          </div>
        </div>
      </div>
    </div>

  </div>
  `;

  // Unter IMO einhängen, wenn vorhanden, sonst nach anchor
  try {
    if (imo && imo.parentNode) {
      imo.parentNode.insertBefore(box, imo.nextSibling);
    } else {
      anchor.parentNode.insertBefore(box, anchor.nextSibling);
    }
  } catch (_) {
    // Notfalls ans Ende
    try { document.body.appendChild(box); } catch (_) {}
  }

  // Slider interaction (leise)
  try {
    const slider = document.getElementById("sunSlider");
    if (slider && !slider.__sunBound) {
      slider.addEventListener("input", () => {
        try { sunRenderSelectedIndex(Number(slider.value)); } catch (_) {}
      });
      slider.__sunBound = true;
    }
  } catch (_) {}

  // Planung öffnen – +48h (Step 1: nur UI/Animation, noch kein Render)
  try {
    const trg = document.getElementById("sunPlanTrigger");
    const body = document.getElementById("sunPlanBody");
    const chev = document.getElementById("sunPlanChevron");
    const KEY = "da_sun_plan_open_v1";

    const setOpen = (open) => {
      if (!trg || !body) return;
      trg.setAttribute("aria-expanded", open ? "true" : "false");
      try { if (chev) chev.style.transform = open ? "rotate(90deg)" : "rotate(0deg)"; } catch (_) {}

      if (open) {
        body.style.opacity = "1";
        // max-height large enough; content is small now, will grow later
        body.style.maxHeight = "760px";
      } else {
        body.style.opacity = "0";
        body.style.maxHeight = "0px";
      }

      try { sessionStorage.setItem(KEY, open ? "1" : "0"); } catch (_) {}

      // Render Planung (+48h) nur wenn geöffnet (keine neuen API Calls)
      try {
        if (open) {
          const raw = (typeof window !== "undefined") ? window.__DA_SUN_RAW__ : null;
          if (raw) sunPlanRenderFromRaw(raw);
        }
      } catch (_) {}
    };

    const getOpen = () => {
      try { return sessionStorage.getItem(KEY) === "1"; } catch (_) { return false; }
    };

    const toggle = () => setOpen(!getOpen());

    if (trg && !trg.__planBound) {
      trg.addEventListener("click", toggle);
      trg.addEventListener("keydown", (e) => {
        const k = e && e.key ? e.key : "";
        if (k === "Enter" || k === " ") { e.preventDefault(); toggle(); }
      });
      trg.__planBound = true;

      // initial state (session-only)
      setOpen(getOpen());
    }
  } catch (_) {}
}

function sunIconForHour(h) {
  // h: { cloud, precipProb, precip, code }
  const pp = Number(h?.precipProb);
  const pr = Number(h?.precip);
  const cc = Number(h?.cloud);

  if (Number.isFinite(pp) && pp >= 50) return "🌧️";
  if (Number.isFinite(pr) && pr > 0.0) return "🌧️";
  if (Number.isFinite(cc)) {
    if (cc < 25) return "☀️";
    if (cc < 60) return "⛅";
    return "☁️";
  }
  return "—";
}

function sunRenderSkeleton() {
  sunEnsureUI();
  const meta = document.getElementById("sunMeta");
  const ticks = document.getElementById("sunTicks");
  if (meta) meta.textContent = "—";
  if (ticks) ticks.innerHTML = "";
}


function sunIconForHourDayNight(h, tUTC, sunriseUTC, sunsetUTC) {
  // Nacht: vor Sunrise / nach Sunset -> 🌙 bei klarem Himmel, sonst ☁️/🌧️ etc.
  try {
    const base = sunIconForHour(h);

    if (!(sunriseUTC instanceof Date) || !(sunsetUTC instanceof Date)) return base;
    if (!Number.isFinite(tUTC)) return base;

    const sr = sunriseUTC.getTime();
    const ss = sunsetUTC.getTime();
    const isNight = (tUTC < sr) || (tUTC > ss);
    if (!isNight) return base;

    // Wetter bleibt Wetter
    if (base === "🌧️") return base;

    const cc = Number(h?.cloud);
    if (Number.isFinite(cc) && cc >= 20) return "☁️";
    return "🌙";
  } catch (_) {
    return sunIconForHour(h);
  }
}

function sunRender(payload) {
  sunEnsureUI();
  const meta = document.getElementById("sunMeta");
  const ticks = document.getElementById("sunTicks");
  const slider = document.getElementById("sunSlider");
  if (!meta || !ticks || !slider) return;

  if (!payload) {
    meta.textContent = "Nicht verfügbar.";
    ticks.innerHTML = "";
    return;
  }

  const { sunriseUTC, sunsetUTC, hours, tz, nowUTC } = payload;

  const sr = sunFmtHHMM(sunriseUTC, tz);
  const ss = sunFmtHHMM(sunsetUTC, tz);

  // Restlicht (nur wenn zwischen sunrise & sunset)
  let rest = "—";
  try {
    const now = nowUTC.getTime();
    const sset = sunsetUTC.getTime();
    const srise = sunriseUTC.getTime();
    if (now >= srise && now <= sset) {
      const diffMin = Math.max(0, Math.round((sset - now) / 60000));
      const hh = Math.floor(diffMin / 60);
      const mm = diffMin % 60;
      rest = `${hh}h ${sunPad2(mm)}m`;
    } else if (now < srise) {
      const diffMin = Math.max(0, Math.round((srise - now) / 60000));
      const hh = Math.floor(diffMin / 60);
      const mm = diffMin % 60;
      rest = `bis Aufgang: ${hh}h ${sunPad2(mm)}m`;
    } else {
      rest = "nach Untergang";
    }
  } catch (_) {}

  meta.innerHTML = `🌅 <b>${sr}</b> &nbsp;→&nbsp; 🌇 <b>${ss}</b> &nbsp;•&nbsp; Restlicht: <b>${rest}</b>`;

  // Axis labels (Mode: photo / 24h)
  try {
    const ax = document.getElementById("sunAxisLabel");
    const mode = (typeof window !== "undefined" && window.__DA_SUN_MODE__ === "24h") ? "24h" : "photo";
    if (ax && ax.children && ax.children.length >= 2) {
      if (mode === "24h") {
        ax.children[0].textContent = "00:00";
        ax.children[1].textContent = "24:00";
      } else {
        ax.children[0].textContent = "−2h";
        ax.children[1].textContent = "+2h";
      }
    }
  } catch (_) {}

  // ticks
  ticks.innerHTML = "";

  // Mode (photo / 24h)
  const mode = (typeof window !== "undefined" && window.__DA_SUN_MODE__ === "24h") ? "24h" : "photo";

  // 10-Minuten Raster für Slider-Auswahl (Sonne = kontinuierlich, Wetter = interpolierter Trend)
  const FINE_STEP_MIN = 10;
  let tStartFine = null;
  let tEndFine = null;
  try{
    const tSunrise = sunriseUTC.getTime();
    const tSunset = sunsetUTC.getTime();
    if (mode === "24h") {
      const y = sunriseUTC.getUTCFullYear();
      const mo = sunriseUTC.getUTCMonth();
      const da = sunriseUTC.getUTCDate();
      tStartFine = Date.UTC(y, mo, da, 0, 0, 0);
      tEndFine = tStartFine + 24 * 60 * 60 * 1000;
    } else {
      const extra = 2 * 60 * 60 * 1000;
      tStartFine = tSunrise - extra;
      tEndFine = tSunset + extra;
    }
  }catch(_){}

  const fineTimes = [];
  try{
    const stepMs = FINE_STEP_MIN * 60 * 1000;
    if (Number.isFinite(tStartFine) && Number.isFinite(tEndFine) && tEndFine > tStartFine) {
      const start = Math.floor(tStartFine / stepMs) * stepMs;
      const end = Math.ceil(tEndFine / stepMs) * stepMs;
      for (let t = start; t <= end; t += stepMs) fineTimes.push(t);
    }
  }catch(_){}

  // Expose for Auto/Render
  try{
    window.__DA_SUN_FINE_STEP_MIN__ = FINE_STEP_MIN;
    window.__DA_SUN_FINE_TIMES__ = fineTimes;
  }catch(_){}

  const maxIdx = Math.max(0, fineTimes.length - 1);
  slider.min = 0;
  slider.max = String(maxIdx);
  slider.step = "1";

  // default: nächster 10-Minuten-Slot ab jetzt
  let defIdx = 0;
  try {
    const nowT = nowUTC.getTime();
    let best = 0;
    let bestDiff = Infinity;

    const stepMs = FINE_STEP_MIN * 60 * 1000;
    const nowR = Math.round(nowT / stepMs) * stepMs;

    for (let i = 0; i < (fineTimes.length || 0); i++) {
      const t = fineTimes[i] || 0;
      const diff = Math.abs(t - nowR);
      if (diff < bestDiff) { bestDiff = diff; best = i; }
    }
    defIdx = best;
  } catch (_) {}
  slider.value = String(defIdx);

  // Mode-aware ticks (Solution B: im 24h-Modus Labels ausdünnen, Icons bleiben)
  const showLabelEvery = (mode === "24h") ? 3 : 1; // 00,03,06,09,12,15,18,21
  const tickCount = (hours?.length || 0);

  // Styling: im 24h-Modus ruhig halten, kein Overflow
  try {
    ticks.style.display = "flex";
    ticks.style.justifyContent = "space-between";
    ticks.style.gap = (mode === "24h") ? "4px" : "6px";
    ticks.style.overflow = "hidden";
  } catch (_) {}

  for (let i = 0; i < tickCount; i++) {
    const h = hours[i];
    const el = document.createElement("div");
    el.style.flex = "1";
    el.style.textAlign = "center";
    el.style.whiteSpace = "nowrap";
    el.style.opacity = (i === defIdx) ? "1" : ".85";
    el.style.minWidth = "0";

    const t = (() => { try { return sunFmtHHMM(sunParseISOToUTC(h.time), tz); } catch (_) { return "—"; } })();
    const tUTC = Date.parse(h?.time || "") || NaN;
    const ic = sunIconForHourDayNight(h, tUTC, sunriseUTC, sunsetUTC);

    const isLabeled = (mode !== "24h") || (i % showLabelEvery === 0);
    const label = isLabeled ? t : "&nbsp;";
    const timeFont = (mode === "24h") ? "11px" : "12px";
    const timeOpacity = (mode === "24h") ? ".85" : ".9";

    el.innerHTML = `<div style="font-weight:600;">${ic}</div><div style="opacity:${timeOpacity}; font-size:${timeFont};">${label}</div>`;
    ticks.appendChild(el);
  }

  // render selection details (minimal)
  sunLastPayload = payload;
  sunLastPayloadKey = payload?.key || "";
  sunRenderSelectedIndex(defIdx);
  try { /* curve drawn in selection */ } catch (_) {}
  try { sunStartAutoPlay(); } catch (_) {}
}


function sunNearestHourIndex(payload, tMs){
  try{
    if (!payload || !Array.isArray(payload.hours) || !payload.hours.length) return 0;
    let best = 0, bestDiff = Infinity;
    for (let i=0;i<payload.hours.length;i++){
      const tt = sunParseISOToUTC(payload.hours[i].time).getTime();
      const d = Math.abs(tt - tMs);
      if (d < bestDiff){ bestDiff = d; best = i; }
    }
    return best;
  }catch(_){ return 0; }
}

function sunInterpFromHourly(payload, tMs){
  const out = { cloud: NaN, precipProb: NaN, precip: NaN, code: null, isExactHour: false };
  try{
    if (!payload || !Array.isArray(payload.hours) || !payload.hours.length) return out;

    const times = payload.hours.map(h => sunParseISOToUTC(h.time).getTime());
    let j = 0;
    for (let i=0;i<times.length;i++){
      if (times[i] <= tMs) j = i;
      if (times[i] > tMs) break;
    }
    const t0 = times[j];
    const h0 = payload.hours[j];
    const t1 = (j+1 < times.length) ? times[j+1] : t0;
    const h1 = (j+1 < times.length) ? payload.hours[j+1] : h0;

    out.isExactHour = (Math.abs(tMs - t0) < 1000);

    const itp = (typeof window !== "undefined" && typeof window.__DA_INTERPOLATE_WEATHER__ === "function")
      ? window.__DA_INTERPOLATE_WEATHER__
      : function(t, a, b, v0, v1){
          if (!isFinite(a) || !isFinite(b) || b === a) return v0;
          const f = Math.max(0, Math.min(1, (t-a)/(b-a)));
          return v0 + (v1-v0)*f;
        };

    const c0 = Number(h0.cloud), c1 = Number(h1.cloud);
    const p0 = Number(h0.precipProb), p1 = Number(h1.precipProb);
    const r0 = Number(h0.precip), r1 = Number(h1.precip);

    out.cloud = (isFinite(c0) && isFinite(c1)) ? itp(tMs, t0, t1, c0, c1) : (isFinite(c0) ? c0 : NaN);
    out.precipProb = (isFinite(p0) && isFinite(p1)) ? itp(tMs, t0, t1, p0, p1) : (isFinite(p0) ? p0 : NaN);
    out.precip = (isFinite(r0) && isFinite(r1)) ? itp(tMs, t0, t1, r0, r1) : (isFinite(r0) ? r0 : NaN);

    out.code = h0 && (h0.code ?? null);
    return out;
  }catch(_){
    return out;
  }
}

function sunRenderSelectedIndex(idx) {
  try {
    const payload = sunLastPayload;
    if (!payload) return;

    const fineTimes = (typeof window !== "undefined" && Array.isArray(window.__DA_SUN_FINE_TIMES__)) ? window.__DA_SUN_FINE_TIMES__ : [];
    const useFine = fineTimes && fineTimes.length;

    const hint = document.getElementById("sunHint");
    const ticks = document.getElementById("sunTicks");
    if (!hint || !ticks) return;

    if (useFine) {
      const i = sunClamp(Number(idx) || 0, 0, fineTimes.length - 1);
      const selT = fineTimes[i];

      const hi = sunNearestHourIndex(payload, selT);
      for (let k = 0; k < ticks.children.length; k++) {
        try { ticks.children[k].style.opacity = (k === hi) ? "1" : ".85"; } catch (_) {}
      }

      const t = sunFmtHHMM(new Date(selT), payload.tz);

      const w = sunInterpFromHourly(payload, selT);
      const cc = w.cloud;
      const pp = w.precipProb;
      const pr = w.precip;

      const approx = w.isExactHour ? "" : "~";
      const ccTxt = Number.isFinite(cc) ? `${approx}${Math.round(cc)}% Bewölkung` : "Bewölkung —";
      const ppTxt = Number.isFinite(pp) ? `${approx}${Math.round(pp)}% Regenrisiko` : "Regenrisiko —";
      const prTxt = Number.isFinite(pr) ? `${approx}${pr.toFixed(1)} mm` : "—";

      
    // Relative Zeit +X (gegenüber Jetzt) dominant anzeigen (Planung)
    let __relTxt = "";
    try{
      const nowBase = Date.now();
      const diffMs = selT - nowBase;
      const sign = diffMs >= 0 ? "+" : "−";
      const absMs = Math.abs(diffMs);
      const hh = Math.floor(absMs / (60*60*1000));
      const mm = Math.round((absMs % (60*60*1000)) / (60*1000));
      __relTxt = `${sign}${hh}h ${mm.toString().padStart(2,"0")}m`;
    }catch(_){ __relTxt = t; }

    hint.innerHTML = `Auswahl <b>${t}</b>: ${ccTxt} • ${ppTxt} • Niederschlag: <b>${prTxt}</b>`;



      try { sunDrawCurve(payload, selT); } catch (_) {}
    } else {
      if (!Array.isArray(payload.hours) || !payload.hours.length) return;

      const i = sunClamp(Number(idx) || 0, 0, payload.hours.length - 1);
      const h = payload.hours[i];

      for (let k = 0; k < ticks.children.length; k++) {
        try { ticks.children[k].style.opacity = (k === i) ? "1" : ".85"; } catch (_) {}
      }

      const t = (() => { try { return sunFmtHHMM(sunParseISOToUTC(h.time), payload.tz); } catch (_) { return "—"; } })();
      const cc = Number(h.cloud);
      const pp = Number(h.precipProb);
      const pr = Number(h.precip);

      const ccTxt = Number.isFinite(cc) ? `${Math.round(cc)}% Bewölkung` : "Bewölkung —";
      const ppTxt = Number.isFinite(pp) ? `${Math.round(pp)}% Regenrisiko` : "Regenrisiko —";
      const prTxt = Number.isFinite(pr) ? `${pr.toFixed(1)} mm` : "—";

      hint.innerHTML = `Auswahl <b>${t}</b>: ${ccTxt} • ${ppTxt} • Niederschlag: <b>${prTxt}</b>`;
try { sunDrawCurve(payload, i); } catch (_) {}
    }
  } catch (_) {}
}



function sunStartAutoPlay() {
  try {
    const slider = document.getElementById("sunSlider");
    if (!slider) return;
    if (sunAutoTimer) return;

    sunAutoTimer = setInterval(() => {
      try {
        const payload = sunLastPayload;
        if (!payload) return;

        const fineTimes = (typeof window !== "undefined" && Array.isArray(window.__DA_SUN_FINE_TIMES__)) ? window.__DA_SUN_FINE_TIMES__ : [];
        const useFine = fineTimes && fineTimes.length;

        if (!useFine && (!Array.isArray(payload.hours) || !payload.hours.length)) return;

        // User hat gerade geschoben -> Auto kurz pausieren
        if (Date.now() - (sunLastUserInteractAt || 0) < 8000) return;

        // Jetzt (Iceland/UTC) -> passendsten Index wählen (10-Min Raster wenn aktiv)
        const nowUtc = new Date(); // UTC-basiert; Island = UTC
        const nowT = nowUtc.getTime();

        let bestIdx = 0;
        let bestDiff = Infinity;

        if (useFine) {
          const stepMin = Number(window.__DA_SUN_FINE_STEP_MIN__) || 10;
          const stepMs = stepMin * 60 * 1000;
          const nowR = Math.round(nowT / stepMs) * stepMs;

          for (let i = 0; i < fineTimes.length; i++) {
            const t = fineTimes[i];
            const d = Math.abs(t - nowR);
            if (d < bestDiff) { bestDiff = d; bestIdx = i; }
          }
        } else {
          const nowIso = nowUtc.toISOString().slice(0, 16);
          const nowHourIso = nowIso.slice(0, 13) + ":00";
          const nowH = sunParseISOToUTC(nowHourIso).getTime();

          for (let i = 0; i < payload.hours.length; i++) {
            const t = sunParseISOToUTC(payload.hours[i].time).getTime();
            const d = Math.abs(t - nowH);
            if (d < bestDiff) { bestDiff = d; bestIdx = i; }
          }
        }

        // Slider + Render (mit Kurve/Marker)
        if (Number(slider.value) !== Number(bestIdx)) {
          slider.value = String(bestIdx);
          sunAutoLastIdx = bestIdx;
          sunRenderSelectedIndex(bestIdx);
        } else {
          // für Puls/Marker minimal neu zeichnen (ohne Wert zu ändern)
          sunRenderSelectedIndex(bestIdx);
        }
      } catch (_) {}
    }, 1000);
  } catch (_) {}
}

// --- Fetch + Mapping ---
async function sunFetchHourly(lat, lon, tz = SUN_TZ) {
  const params = new URLSearchParams({
    latitude: lat.toFixed(4),
    longitude: lon.toFixed(4),
    hourly: "cloudcover,precipitation_probability,precipitation,weathercode",
    timezone: tz,
  });
  const url = `${SUN_API_BASE}?${params.toString()}`;
  const res = await fetch(url, { cache: "no-cache" });
  if (!res.ok) throw new Error(`SunWeather HTTP ${res.status}`);
  const js = await res.json();
  return js?.hourly || null;
}

function sunNormalizeHourly(hourly) {
  // returns array of { time, cloud, precipProb, precip, code }
  if (!hourly || !Array.isArray(hourly.time)) return [];
  const t = hourly.time;
  const cc = hourly.cloudcover || hourly.cloud_cover || [];
  const pp = hourly.precipitation_probability || hourly.precipitationProbability || [];
  const pr = hourly.precipitation || [];
  const wc = hourly.weathercode || hourly.weather_code || [];

  const out = [];
  for (let i = 0; i < t.length; i++) {
    out.push({
      time: t[i],
      cloud: cc[i],
      precipProb: pp[i],
      precip: pr[i],
      code: wc[i],
    });
  }
  return out;
}

function sunFmtISOKeyInTz(dateObj, tz = SUN_TZ) {
  try {
    const parts = new Intl.DateTimeFormat("en-CA", {
      timeZone: tz,
      year: "numeric",
      month: "2-digit",
      day: "2-digit",
      hour: "2-digit",
      minute: "2-digit",
      hour12: false,
    }).formatToParts(dateObj).reduce((a, p) => (a[p.type] = p.value, a), {});
    const y = parts.year, mo = parts.month, d = parts.day, hh = parts.hour, mm = parts.minute;
    // Open-Meteo hourly.time ist i.d.R. "YYYY-MM-DDTHH:MM" in der gewählten TZ
    return `${y}-${mo}-${d}T${hh}:${mm}`;
  } catch (_) {
    // Fallback (lokal): nicht perfekt, aber robust ohne Console-Spam
    const y = dateObj.getFullYear();
    const mo = sunPad2(dateObj.getMonth() + 1);
    const d = sunPad2(dateObj.getDate());
    const hh = sunPad2(dateObj.getHours());
    const mm = sunPad2(dateObj.getMinutes());
    return `${y}-${mo}-${d}T${hh}:${mm}`;
  }
}

function sunBuildHourlySlots(hoursAll, axisStartUTC, axisEndUTC, tz = SUN_TZ) {
  // Baut stündliche Slots über das komplette Fenster (z.B. -2h ... +2h),
  // und mappt Open-Meteo-Werte über den Zeit-Key in derselben TZ.
  const map = new Map();
  for (const h of hoursAll || []) {
    if (h && typeof h.time === "string") map.set(h.time, h);
  }

  const out = [];
  const start = axisStartUTC instanceof Date ? axisStartUTC.getTime() : NaN;
  const end = axisEndUTC instanceof Date ? axisEndUTC.getTime() : NaN;
  if (!Number.isFinite(start) || !Number.isFinite(end) || end <= start) return out;

  // auf volle Stunde runden (UTC), Anzeige/Matching erfolgt in TZ über Keys
  const oneH = 60 * 60 * 1000;
  let t = Math.floor(start / oneH) * oneH;
  const tEnd = Math.ceil(end / oneH) * oneH;

  for (; t <= tEnd; t += oneH) {
    const d = new Date(t);
    // Wir matchen per Key in Ziel-TZ
    const key = sunFmtISOKeyInTz(d, tz);
    const found = map.get(key);
    out.push(found ? found : { time: key, cloud: null, precipProb: null, precip: null, code: null });
  }
  return out;
}


function sunBuildHourlySlotsExclusive(hoursAll, axisStartUTC, axisEndUTC, tz = SUN_TZ) {
  // Wie sunBuildHourlySlots, aber axisEnd wird als exklusiv behandelt (t < tEnd).
  // Sinn: 24h-Modus zeigt 00:00..23:00 ohne doppeltes 24:00 (= 00:00 vom Folgetag).
  const map = new Map();
  for (const h of hoursAll || []) {
    if (h && typeof h.time === "string") map.set(h.time, h);
  }

  const out = [];
  const start = axisStartUTC instanceof Date ? axisStartUTC.getTime() : NaN;
  const end = axisEndUTC instanceof Date ? axisEndUTC.getTime() : NaN;
  if (!Number.isFinite(start) || !Number.isFinite(end) || end <= start) return out;

  const oneH = 60 * 60 * 1000;
  let t = Math.floor(start / oneH) * oneH;
  const tEnd = Math.ceil(end / oneH) * oneH;

  for (; t < tEnd; t += oneH) {
    const d = new Date(t);
    const key = sunFmtISOKeyInTz(d, tz);
    const found = map.get(key);
    out.push(found ? found : { time: key, cloud: null, precipProb: null, precip: null, code: null });
  }
  return out;
}


function sunRenderFromRaw(raw) {
  try {
    if (!raw) return;
    const mode = (typeof window !== "undefined" && window.__DA_SUN_MODE__ === "24h") ? "24h" : "photo";

    // Axis window
    let axisStartUTC, axisEndUTC;
    if (mode === "24h") {
      // Day in Iceland TZ (UTC): 00:00 .. 24:00
      const d = sunNowInTz(SUN_TZ); // {y,m,d}
      const dayStart = Date.UTC(d.y, d.m - 1, d.d, 0, 0, 0);
      axisStartUTC = new Date(dayStart);
      axisEndUTC = new Date(dayStart + 24 * 60 * 60 * 1000);
    } else {
      const extra = 2 * 60 * 60 * 1000;
      axisStartUTC = new Date(raw.sunriseUTC.getTime() - extra);
      axisEndUTC = new Date(raw.sunsetUTC.getTime() + extra);
    }

    const slots = (mode === "24h")
      ? sunBuildHourlySlotsExclusive(raw.hoursAll, axisStartUTC, axisEndUTC, SUN_TZ)
      : sunBuildHourlySlots(raw.hoursAll, axisStartUTC, axisEndUTC, SUN_TZ);
    const nowUTC = new Date();

    sunRender({
      key: raw.key,
      lat: raw.lat,
      lon: raw.lon,
      sunriseUTC: raw.sunriseUTC,
      sunsetUTC: raw.sunsetUTC,
      hours: slots || [],
      tz: raw.tz || SUN_TZ,
      nowUTC,
    });

    // Planung (+48h) aktualisieren, falls geöffnet
    try {
      if (sunPlanIsOpen && sunPlanIsOpen()) {
        sunPlanRenderFromRaw(raw);
      }
    } catch (_) {}
  } catch (_) {}
}




function sunFmtRelFromSpan(relMs){
  try{
    const diff = Number(relMs);
    const sign = diff >= 0 ? "+" : "−";
    const abs = Math.abs(diff);
    const h = Math.floor(abs / (60*60*1000));
    const m = Math.round((abs % (60*60*1000)) / (60*1000));
    if (h <= 0) return `${sign}${m}m`;
    return `${sign}${h}h ${m.toString().padStart(2,"0")}m`;
  }catch(_){ return ""; }
}

function sunFmtRelFromNow(targetMs){
  try{
    const now = Date.now();
    const diff = Number(targetMs) - now;
    const sign = diff >= 0 ? "+" : "−";
    const abs = Math.abs(diff);
    const h = Math.floor(abs / (60*60*1000));
    const m = Math.round((abs % (60*60*1000)) / (60*1000));
    if (h <= 0) return `${sign}${m}m`;
    return `${sign}${h}h ${m.toString().padStart(2,"0")}m`;
  }catch(_){ return ""; }
}

// -------------------------
// Planung (+48h) – Step 2
// Gleiche Render-Logik, nur Zeit versetzt (keine neuen API Calls)
// -------------------------

function sunPlanIsOpen(){
  try{
    const trg = document.getElementById("sunPlanTrigger");
    return !!(trg && trg.getAttribute("aria-expanded") === "true");
  }catch(_){ return false; }
}

function sunPlanTargetDate(offsetDays){
  try{
    const d = sunNowInTz(SUN_TZ); // {y,m,d}
    const base = Date.UTC(d.y, d.m - 1, d.d, 0, 0, 0);
    const t = base + (offsetDays * 24 * 60 * 60 * 1000);
    const dt = new Date(t);
    return { y: dt.getUTCFullYear(), m: dt.getUTCMonth() + 1, d: dt.getUTCDate() };
  }catch(_){
    const dt = new Date(Date.now() + offsetDays * 24*60*60*1000);
    return { y: dt.getUTCFullYear(), m: dt.getUTCMonth() + 1, d: dt.getUTCDate() };
  }
}

function sunPlanDrawCurve(payload, selectedMs){
  try{
    const c = document.getElementById("sunPlanCurve");
    if (!c || !c.getContext) return;
    const ctx = c.getContext("2d");
    if (!ctx) return;

    const { sunriseUTC, sunsetUTC, axisStartUTC, axisEndUTC } = payload || {};
    const hasAxis = (axisStartUTC instanceof Date) && (axisEndUTC instanceof Date);
    const hasSun = (sunriseUTC instanceof Date) && (sunsetUTC instanceof Date);
    if (!hasAxis && !hasSun) return;

    const w = c.width || 680;
    const h = c.height || 90;
    ctx.clearRect(0, 0, w, h);

    const padL = 26, padR = 10, padT = 10, padB = 18;
    const x0 = padL, y0 = h - padB, x1 = w - padR, y1 = padT;

    const mode = (typeof window !== "undefined" && window.__DA_SUN_MODE__ === "24h") ? "24h" : "photo";
    let tStart, tEnd;
    if (hasAxis) {
      tStart = axisStartUTC.getTime();
      tEnd = axisEndUTC.getTime();
    } else if (mode === "24h") {
      const y = sunriseUTC.getUTCFullYear();
      const mo = sunriseUTC.getUTCMonth();
      const da = sunriseUTC.getUTCDate();
      tStart = Date.UTC(y, mo, da, 0, 0, 0);
      tEnd = tStart + 24 * 60 * 60 * 1000;
    } else {
      const extra = 2 * 60 * 60 * 1000;
      tStart = sunriseUTC.getTime() - extra;
      tEnd = sunsetUTC.getTime() + extra;
    }

    const toX = (t) => x0 + ((t - tStart) / Math.max(1, (tEnd - tStart))) * (x1 - x0);
    const toY = (altDeg) => {
      const a = Math.max(-6, Math.min(60, altDeg));
      const f = (a + 6) / 66;
      return y0 - f * (y0 - y1);
    };

    // baseline
    ctx.globalAlpha = 0.35;
    ctx.lineWidth = 1;
    ctx.strokeStyle = "rgba(255,255,255,0.20)";
    ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y0); ctx.stroke();

    // curve
    ctx.globalAlpha = 0.9;
    ctx.lineWidth = 2;
    ctx.strokeStyle = "rgba(255,210,80,0.75)";
    ctx.beginPath();
    const steps = 80;
    for (let s = 0; s <= steps; s++) {
      const t = tStart + (s / steps) * (tEnd - tStart);
      const alt = sunCalcAltitudeDegUTC(payload.lat, payload.lon, new Date(t));
      const x = toX(t);
      const y = toY(alt);
      if (s === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
    }
    ctx.stroke();

    // selection marker (weiß, ruhig)
    try{
      const tSel = Number(selectedMs);
      if (Number.isFinite(tSel)) {
        const xSel = toX(tSel);

        ctx.globalAlpha = 0.55;
        ctx.lineWidth = 2;
        ctx.strokeStyle = "rgba(255,255,255,0.35)";
        ctx.beginPath(); ctx.moveTo(xSel, y1); ctx.lineTo(xSel, y0); ctx.stroke();

        const altSel = sunCalcAltitudeDegUTC(payload.lat, payload.lon, new Date(tSel));
        const ySel = Number.isFinite(altSel) ? toY(altSel) : y0;
        ctx.globalAlpha = 0.9;
        ctx.fillStyle = "rgba(255,255,255,0.85)";
        ctx.beginPath(); ctx.arc(xSel, ySel, 2.8, 0, Math.PI * 2); ctx.fill();
      }
    }catch(_){}
  }catch(_){}
}

function sunPlanEnsureUIBind(){
  try{
    const slider = document.getElementById("sunPlanSlider");
    if (slider && !slider.__sunPlanBound){
      slider.addEventListener("input", (e) => {
        try { sunPlanRenderSelectedIndex(Number(e.target.value) || 0); } catch (_) {}
        try { sunStopAutoPlay(); } catch (_) {}
      });
      slider.__sunPlanBound = true;
    }
  }catch(_){}
}

function sunPlanBuildFineTimes(payload){
  const fineTimes = [];
  try{
    const mode = (typeof window !== "undefined" && window.__DA_SUN_MODE__ === "24h") ? "24h" : "photo";
    const FINE_STEP_MIN = 10;
    const stepMs = FINE_STEP_MIN * 60 * 1000;

    let tStartFine = null, tEndFine = null;

    const hasAxis = (payload.axisStartUTC instanceof Date) && (payload.axisEndUTC instanceof Date);
    if (hasAxis) {
      tStartFine = payload.axisStartUTC.getTime();
      tEndFine = payload.axisEndUTC.getTime();
    }

    const tSunrise = (payload.sunriseUTC instanceof Date) ? payload.sunriseUTC.getTime() : NaN;
    const tSunset = (payload.sunsetUTC instanceof Date) ? payload.sunsetUTC.getTime() : NaN;

    if (mode === "24h") {
      const y = payload.sunriseUTC.getUTCFullYear();
      const mo = payload.sunriseUTC.getUTCMonth();
      const da = payload.sunriseUTC.getUTCDate();
      tStartFine = Date.UTC(y, mo, da, 0, 0, 0);
      tEndFine = tStartFine + 24 * 60 * 60 * 1000;
    } else {
      const extra = 2 * 60 * 60 * 1000;
      tStartFine = tSunrise - extra;
      tEndFine = tSunset + extra;
    }

    if (Number.isFinite(tStartFine) && Number.isFinite(tEndFine) && tEndFine > tStartFine) {
      const start = Math.floor(tStartFine / stepMs) * stepMs;
      const end = Math.ceil(tEndFine / stepMs) * stepMs;
      for (let t = start; t <= end; t += stepMs) fineTimes.push(t);
    }

    return { fineTimes, stepMin: FINE_STEP_MIN };
  }catch(_){ return { fineTimes, stepMin: 10 }; }
}

function sunPlanRender(payload){
  try{
    if (!payload) return;

    sunPlanEnsureUIBind();

    const axis = document.getElementById("sunPlanAxis");
    const slider = document.getElementById("sunPlanSlider");
    const ticks = document.getElementById("sunPlanTicks");
    const hint = document.getElementById("sunPlanHint");
    const canvas = document.getElementById("sunPlanCurve");
    if (!axis || !slider || !ticks || !hint || !canvas) return;

    const mode = (typeof window !== "undefined" && window.__DA_SUN_MODE__ === "24h") ? "24h" : "photo";
    try{
      axis.innerHTML = (payload.axisStartUTC instanceof Date && payload.axisEndUTC instanceof Date) ? `<span>+0h</span><span>+48h</span>` : ((mode === "24h") ? `<span>00:00</span><span>24:00</span>` : `<span>−2h</span><span>+2h</span>`);
    }catch(_){}

    const bt = sunPlanBuildFineTimes(payload);
    const fineTimes = bt.fineTimes || [];
    try{
      window.__DA_SUN_PLAN_FINE_TIMES__ = fineTimes;
      window.__DA_SUN_PLAN_LAST_PAYLOAD__ = payload;
      window.__DA_SUN_PLAN_STEP_MIN__ = bt.stepMin;
    }catch(_){}

    slider.min = 0;
    slider.max = String(Math.max(0, fineTimes.length - 1));
    slider.step = "1";

    // ticks: hourly icons
    ticks.innerHTML = "";
    try{
      const hours = payload.hours || [];
      for (let i = 0; i < hours.length; i++) {
        const h = hours[i];
        const tLab = (()=>{ try { return sunFmtHHMM(sunParseISOToUTC(h.time), payload.tz); } catch(_){ return ""; } })();
        const hasAxis = (payload.axisStartUTC instanceof Date) && (payload.axisEndUTC instanceof Date);
        let label = "";
        if (hasAxis) {
          const off = i + 1; // Slots starten bei nächster voller Stunde => erste = +1h
          if (off === 1 || off === 48 || (off % 6 === 0)) label = `+${off}h`;
        } else {
          label = (mode === "24h") ? (i % 3 === 0 ? tLab : "") : tLab;
        }
        const emoji = (()=>{ try { return sunIconForHour(h, payload); } catch(_){ return "•"; } })();

        const el = document.createElement("div");
        el.style.flex = "1";
        el.style.minWidth = "0";
        el.style.textAlign = "center";
        el.style.opacity = ".92";
        el.innerHTML = `<div style="font-size:14px; line-height:1;">${emoji}</div><div style="margin-top:2px;">${label}</div>`;
        ticks.appendChild(el);
      }
    }catch(_){}

    // default selection: now+48 rounded to 10min
    let defIdx = 0;
    try{
      const stepMs = (bt.stepMin || 10) * 60 * 1000;
      const nowT = (payload.nowUTC instanceof Date ? payload.nowUTC.getTime() : Date.now());
      const nowR = Math.round(nowT / stepMs) * stepMs;
      let best = 0, bestDiff = Infinity;
      for (let i=0;i<fineTimes.length;i++){
        const d = Math.abs((fineTimes[i]||0) - nowR);
        if (d < bestDiff){ bestDiff = d; best = i; }
      }
      defIdx = best;
    }catch(_){}

    slider.value = String(defIdx);
    sunPlanRenderSelectedIndex(defIdx);

  }catch(_){}
}

function sunPlanNearestHourIndex(payload, tMs){
  try{
    if (!payload || !Array.isArray(payload.hours) || !payload.hours.length) return 0;
    let best = 0, bestDiff = Infinity;
    for (let i=0;i<payload.hours.length;i++){
      const tt = sunParseISOToUTC(payload.hours[i].time).getTime();
      const d = Math.abs(tt - tMs);
      if (d < bestDiff){ bestDiff = d; best = i; }
    }
    return best;
  }catch(_){ return 0; }
}

function sunPlanInterpFromHourly(payload, tMs){
  const out = { cloud: NaN, precipProb: NaN, precip: NaN, isExactHour: false };
  try{
    if (!payload || !Array.isArray(payload.hours) || !payload.hours.length) return out;
    const times = payload.hours.map(h => sunParseISOToUTC(h.time).getTime());
    let j = 0;
    for (let i=0;i<times.length;i++){
      if (times[i] <= tMs) j = i;
      if (times[i] > tMs) break;
    }
    const t0 = times[j];
    const h0 = payload.hours[j];
    const t1 = (j+1 < times.length) ? times[j+1] : t0;
    const h1 = (j+1 < times.length) ? payload.hours[j+1] : h0;

    out.isExactHour = (Math.abs(tMs - t0) < 1000);

    const lerp = (a,b,f)=>a+(b-a)*f;
    const f = (t1 === t0) ? 0 : Math.max(0, Math.min(1, (tMs - t0) / (t1 - t0)));

    const c0 = Number(h0.cloud), c1 = Number(h1.cloud);
    const p0 = Number(h0.precipProb), p1 = Number(h1.precipProb);
    const r0 = Number(h0.precip), r1 = Number(h1.precip);

    out.cloud = (isFinite(c0) && isFinite(c1)) ? lerp(c0,c1,f) : (isFinite(c0) ? c0 : NaN);
    out.precipProb = (isFinite(p0) && isFinite(p1)) ? lerp(p0,p1,f) : (isFinite(p0) ? p0 : NaN);
    out.precip = (isFinite(r0) && isFinite(r1)) ? lerp(r0,r1,f) : (isFinite(r0) ? r0 : NaN);
    return out;
  }catch(_){ return out; }
}

function sunPlanRenderSelectedIndex(idx){
  try{
    const payload = (typeof window !== "undefined" && window.__DA_SUN_PLAN_LAST_PAYLOAD__) ? window.__DA_SUN_PLAN_LAST_PAYLOAD__ : null;
    const fineTimes = (typeof window !== "undefined" && Array.isArray(window.__DA_SUN_PLAN_FINE_TIMES__)) ? window.__DA_SUN_PLAN_FINE_TIMES__ : [];
    const hint = document.getElementById("sunPlanHint");
    const ticks = document.getElementById("sunPlanTicks");
    if (!payload || !fineTimes.length || !hint || !ticks) return;

    const i = sunClamp(Number(idx) || 0, 0, fineTimes.length - 1);
    const selT = fineTimes[i];

    const hi = sunPlanNearestHourIndex(payload, selT);
    for (let k=0;k<ticks.children.length;k++){
      try{ ticks.children[k].style.opacity = (k === hi) ? "1" : ".85"; }catch(_){}
    }

    const t = sunFmtHHMM(new Date(selT), payload.tz);
    const w = sunPlanInterpFromHourly(payload, selT);

    const approx = w.isExactHour ? "" : "~";
    const ccTxt = Number.isFinite(w.cloud) ? `${approx}${Math.round(w.cloud)}% Bewölkung` : "Bewölkung —";
    const ppTxt = Number.isFinite(w.precipProb) ? `${approx}${Math.round(w.precipProb)}% Regenrisiko` : "Regenrisiko —";
    const prTxt = Number.isFinite(w.precip) ? `${approx}${w.precip.toFixed(1)} mm` : "—";

    {
      const hasAxis = (payload.axisStartUTC instanceof Date) && (payload.axisEndUTC instanceof Date);
      if (hasAxis) {
        const span = payload.axisEndUTC.getTime() - payload.axisStartUTC.getTime();
        const relMs = (span > 0 && fineTimes.length > 1) ? (i / (fineTimes.length - 1)) * span : (selT - payload.axisStartUTC.getTime());
        hint.innerHTML = `Auswahl <b>${sunFmtRelFromSpan(relMs)}</b><span style="opacity:.55;font-weight:400;"> (${t})</span>: ${ccTxt} • ${ppTxt} • Niederschlag: <b>${prTxt}</b>`;
      } else {
        hint.innerHTML = `Auswahl <b>${sunFmtRelFromNow(selT)}</b><span style="opacity:.55;font-weight:400;"> (${t})</span>: ${ccTxt} • ${ppTxt} • Niederschlag: <b>${prTxt}</b>`;
      }
    }

    try{ sunPlanDrawCurve(payload, selT); }catch(_){}
  }catch(_){}
}

function sunPlanRenderFromRaw(raw){
  try{
    if (!raw) return;
    const body = document.getElementById("sunPlanBody");
    if (!body) return;

    // Ziel: nächste 48h ab JETZT (nicht „in 2 Tagen“)
    const nowMs = Date.now();
    const axisStartUTC = new Date(nowMs);
    const axisEndUTC = new Date(nowMs + 48 * 60 * 60 * 1000);

    // Slots aus vorhandenen Open‑Meteo Stunden (keine neuen Calls)
    // Icons/Slots beginnen bei der NÄCHSTEN vollen Stunde: +1h ... +48h
    const H = 60 * 60 * 1000;
    const startSlotsUTC = new Date(Math.ceil(nowMs / H) * H);
    const endSlotsUTC = new Date(startSlotsUTC.getTime() + 48 * H);
    const slots = sunBuildHourlySlots(raw.hoursAll, startSlotsUTC, endSlotsUTC, SUN_TZ);

    // Sonnenzeiten nur als Fallback (für bestehende Logik, falls gebraucht)
    let sTimes = null;
    try{
      const d0 = sunNowInTz(SUN_TZ);
      sTimes = sunCalcSunTimesUTC(raw.lat, raw.lon, d0.y, d0.m, d0.d);
    }catch(_){}

    sunPlanRender({
      key: raw.key + "_p48",
      lat: raw.lat,
      lon: raw.lon,
      sunriseUTC: (sTimes && sTimes.sunrise instanceof Date) ? sTimes.sunrise : new Date(nowMs),
      sunsetUTC: (sTimes && sTimes.sunset instanceof Date) ? sTimes.sunset : new Date(nowMs + 12*60*60*1000),
      axisStartUTC,
      axisEndUTC,
      hours: slots || [],
      tz: raw.tz || SUN_TZ,
      nowUTC: new Date(nowMs),
    });
  }catch(_){}
}

async function sunUpdate(lat, lon, force = false) {
  try {
    sunEnsureUI();

    const now = Date.now();
    const key = `${lat.toFixed(3)},${lon.toFixed(3)}`;

    if (!force) {
      if (now - sunLastFetchAt < SUN_THROTTLE_MS) return;
      if (key === sunLastKey && now - sunLastFetchAt < (SUN_THROTTLE_MS * 2)) return;
    }

    sunLastFetchAt = now;
    sunLastKey = key;

    // Sonnenzeiten für "heute" in Island-TZ
    const d = sunNowInTz(SUN_TZ);
    const times = sunCalcSunTimesUTC(lat, lon, d.y, d.m, d.d);

    const hourlyRaw = await sunFetchHourly(lat, lon, SUN_TZ);
    
    const hoursAll = sunNormalizeHourly(hourlyRaw);
    // Raw speichern (für Umschalten ohne neue API Calls)
    try{
      window.__DA_SUN_RAW__ = {
        key,
        lat,
        lon,
        sunriseUTC: times.sunrise,
        sunsetUTC: times.sunset,
        hoursAll: (Array.isArray(hoursAll) ? hoursAll : []),
        tz: SUN_TZ,
      };
    }catch(_){}

    // Rendern je nach Modus (photo / 24h) – Slots werden lokal gebaut
    try { sunRenderFromRaw(window.__DA_SUN_RAW__); } catch (_) {}
  } catch (_) {
    // leise bleiben – kein Error-Spam in der Konsole
    try { sunRenderSkeleton(); } catch (_) {}
  }
}

function sunInstallHooks() {
  if (sunHooksInstalled) return;
  if (typeof marker === "undefined" || !marker) return;

  sunEnsureUI();

  const onMove = () => {
    try {
      const p = marker.getLatLng();
      sunUpdate(p.lat, p.lng, false);
    } catch (_) {}
  };

  try { marker.on("drag", onMove); } catch (_) {}
  try { marker.on("dragend", onMove); } catch (_) {}

  // updateMap hooken (nur wenn nicht schon)
  try {
    if (typeof updateMap === "function" && !updateMap.__sunWrapped) {
      const _u = updateMap;
      const wrapped = function(lat, lon, accuracyMeters = null) {
        const r = _u(lat, lon, accuracyMeters);
        try { sunUpdate(lat, lon, true); } catch (_) {}
        return r;
      };
      wrapped.__sunWrapped = true;
      updateMap = wrapped;
    }
  } catch (_) {}

  // Initial
  try {
    const p = marker.getLatLng();
    sunUpdate(p.lat, p.lng, true);
  } catch (_) {}

  sunHooksInstalled = true;
}

// warten bis marker existiert
const sunWait = setInterval(() => {
  if (typeof marker !== "undefined" && marker) {
    sunInstallHooks();
    clearInterval(sunWait);
  }
}, 220);

// UI early
document.addEventListener("DOMContentLoaded", () => {
  try { sunEnsureUI(); } catch (_) {}
});



// =============================
// Map resize hook for collapsible panel
// =============================
(function(){
  'use strict';
  document.addEventListener('da:panel', function(ev){
    const d = ev && ev.detail ? ev.detail : null;
    if (!d || d.panelId !== 'map' || !d.open) return;

    // Leaflet needs a nudge after the panel expands
    setTimeout(function(){
      try{
        const m = window.__DA_LEAFLET_MAP__;
        if (m && typeof m.invalidateSize === 'function') m.invalidateSize();
      }catch(_){}
    }, 230);
  });
})();

// =============================
// Collapsible Panels (Step 2)
// - Additiv, session-only (sessionStorage)
// - Soft animation (~200ms) via max-height + opacity
// - Multiple panels can be open simultaneously
// =============================
(function(){
  'use strict';

  const PANEL_STATE_KEY = 'droneampel_panels_v1';
  const panelState = loadPanelState();
  const registry = Object.create(null); // panelId -> panelEl

  function safeParse(json){
    try { return JSON.parse(json); } catch(_){ return null; }
  }

  function loadPanelState(){
    try{
      const raw = sessionStorage.getItem(PANEL_STATE_KEY);
      const obj = raw ? safeParse(raw) : null;
      return (obj && typeof obj === 'object') ? obj : {};
    }catch(_){
      return {};
    }
  }

  function savePanelState(state){
    try{
      sessionStorage.setItem(PANEL_STATE_KEY, JSON.stringify(state || {}));
    }catch(_){}
  }

  function isOpen(panelId, fallbackOpen=true){
    if (!panelId) return fallbackOpen;
    if (Object.prototype.hasOwnProperty.call(panelState, panelId)){
      return !!panelState[panelId];
    }
    return !!fallbackOpen;
  }

  function emit(panelId, open){
    try{
      document.dispatchEvent(new CustomEvent('da:panel', { detail: { panelId: panelId, open: !!open } }));
    }catch(_){}
  }

  function setOpen(panelId, open){
    if (!panelId) return;
    panelState[panelId] = !!open;
    savePanelState(panelState);
    applyPanel(panelId);
    emit(panelId, open);
  }

  function ensurePrepared(panelEl){
    if (!panelEl || panelEl.dataset.panelPrepared === '1') return;

    const body = panelEl.querySelector('[data-panel-body]');
    if (!body) { panelEl.dataset.panelPrepared = '1'; return; }

    body.style.overflow = 'hidden';
    body.style.willChange = 'max-height, opacity';
    body.style.transition = 'max-height 200ms ease, opacity 200ms ease';

    const btn = panelEl.querySelector('[data-panel-toggle]');
    if (btn){
      btn.style.border = '1px solid rgba(255,255,255,0.12)';
      btn.style.background = 'rgba(255,255,255,0.06)';
      btn.style.color = 'inherit';
      btn.style.borderRadius = '999px';
      btn.style.width = '28px';
      btn.style.height = '28px';
      btn.style.display = 'inline-flex';
      btn.style.alignItems = 'center';
      btn.style.justifyContent = 'center';
      btn.style.cursor = 'pointer';
      btn.style.lineHeight = '1';
      btn.style.padding = '0';
      btn.style.userSelect = 'none';
      btn.style.transition = 'transform 200ms ease, opacity 200ms ease';
      btn.setAttribute('aria-expanded', 'true');
    }

    panelEl.dataset.panelPrepared = '1';
  }

  function applyPanel(panelId){
    const panelEl = registry[panelId] || document.querySelector('[data-panel-id="'+panelId+'"][data-panel-collapsible="1"]');
    if (!panelEl) return;

    ensurePrepared(panelEl);

    const body = panelEl.querySelector('[data-panel-body]');
    if (!body) return;

    const open = isOpen(panelId, true);

    // Update chevron / aria
    const btn = panelEl.querySelector('[data-panel-toggle="'+panelId+'"]') || panelEl.querySelector('[data-panel-toggle]');
    if (btn){
      btn.setAttribute('aria-expanded', open ? 'true' : 'false');
      btn.style.transform = open ? 'rotate(0deg)' : 'rotate(-90deg)';
      btn.style.opacity = open ? '1' : '0.9';
    }

    // Measure & animate
    if (open){
      body.style.opacity = '1';
      body.style.maxHeight = '0px';
      requestAnimationFrame(function(){
        const h = body.scrollHeight;
        body.style.maxHeight = (h > 0 ? h : 0) + 'px';
      });
    }else{
      const h = body.scrollHeight;
      body.style.maxHeight = (h > 0 ? h : 0) + 'px';
      requestAnimationFrame(function(){
        body.style.maxHeight = '0px';
        body.style.opacity = '0';
      });
    }
  }

  // Called by feature boxes when they are created
  function register(panelEl, panelId, defaultOpen=true){
    if (!panelEl || !panelId) return;

    registry[panelId] = panelEl;

    // If state not set yet, set default (session-only)
    if (!Object.prototype.hasOwnProperty.call(panelState, panelId)){
      panelState[panelId] = !!defaultOpen;
      savePanelState(panelState);
    }

    applyPanel(panelId);
  }

  // Event delegation: Buttons/Links mit data-panel-toggle="panelId"
  document.addEventListener('click', function(ev){
    const t = ev.target && ev.target.closest ? ev.target.closest('[data-panel-toggle]') : null;
    if (!t) return;

    const panelId = t.getAttribute('data-panel-toggle') || '';
    if (!panelId) return;

    // prevent accidental form submission / focus weirdness
    ev.preventDefault();

    const next = !isOpen(panelId, true);
    setOpen(panelId, next);
  });

  // Expose hooks
  window.__DA_PANEL__ = window.__DA_PANEL__ || {};
  window.__DA_PANEL__.isOpen = isOpen;
  window.__DA_PANEL__.setOpen = setOpen;
  window.__DA_PANEL__.register = register;
})();


// =============================
// Sun Extended Timeline (Step 4 – 24h + Live + 10min)
// Additiv – keine bestehende Funktion wird ersetzt
// =============================
(function(){
  'use strict';

  // ---- MODE STATE ----
  let __DA_SUN_MODE__ = 'photo'; // photo | 24h
  try{ window.__DA_SUN_MODE__ = __DA_SUN_MODE__; }catch(_){ }
  // sync label to current mode (button is rendered dynamically later; delegation will still work)
  try{
    document.addEventListener('da:nowtick', function once(){
      const t = document.getElementById('sunModeToggle') || document.querySelector('[data-sun-mode-toggle="1"]');
      if (t) { t.textContent = (window.__DA_SUN_MODE__ === 'photo') ? 'Foto' : '24h'; document.removeEventListener('da:nowtick', once); }
    });
  }catch(_){}


  document.addEventListener('click', function(ev){
    const t = ev.target && ev.target.closest ? ev.target.closest('#sunModeToggle,[data-sun-mode-toggle="1"]') : null;
    if (!t) return;

    ev.preventDefault();

    __DA_SUN_MODE__ = (__DA_SUN_MODE__ === 'photo') ? '24h' : 'photo';
    try{ window.__DA_SUN_MODE__ = __DA_SUN_MODE__; }catch(_){ }
    t.textContent = (__DA_SUN_MODE__ === 'photo') ? 'Foto' : '24h';

    try{
      document.dispatchEvent(new CustomEvent('da:sunmode', { detail:{ mode: __DA_SUN_MODE__ }}));
    }catch(e){}
  });

  // ---- LIVE MARKER ----
  function emitNow(){
    try{
      document.dispatchEvent(new CustomEvent('da:nowtick', { detail:{ now: Date.now() }}));
    }catch(e){}
  }
  setInterval(emitNow, 1000);


  // Re-render on mode change without refetch
  document.addEventListener('da:sunmode', function(){
    try{
      if (window.__DA_SUN_RAW__) sunRenderFromRaw(window.__DA_SUN_RAW__);
    }catch(_){}
  });


  // ---- TIME GRID HELPER ----
  function roundTo10Min(ts){
    const d = new Date(ts);
    const m = d.getUTCMinutes();
    const rounded = Math.round(m/10)*10;
    d.setUTCMinutes(rounded);
    d.setUTCSeconds(0);
    return d.getTime();
  }

  // ---- WEATHER INTERPOLATION HELPER ----
  window.__DA_INTERPOLATE_WEATHER__ = function(t, t0, t1, v0, v1){
    if (!isFinite(t0) || !isFinite(t1) || t1 === t0) return v0;
    const f = Math.max(0, Math.min(1, (t - t0) / (t1 - t0)));
    return v0 + (v1 - v0) * f;
  };

})();

/* pad-step25:............................................................................................................................................................................................................................*/

/* pad ........................................................................................ */

/* pad */


// =============================
// AURORA BOX (KP + Wolken) – 48h Planung
// Offiziell: NOAA / SWPC (planetary K-index 3-day)
// Standort: Wolken/Regen via Open-Meteo (wie Sun/Wind)
// Additiv – keine bestehende Funktion wird ersetzt
// =============================
(function(){
  'use strict';

  const AURORA_PANEL_ID = 'aurora';
  const AURORA_KP_URLS_REMOTE = [
  "https://services.swpc.noaa.gov/products/noaa-planetary-k-index.json",
  "https://services.swpc.noaa.gov/products/noaa-planetary-k-index-forecast.json"
];

// Local-first (silent) for localhost dev: accept NOAA original filenames and our short aliases.
const AURORA_KP_URLS_LOCAL = [
  "./data/noaa-planetary-k-index.json",
  "./data/noaa-planetary-k-index-forecast.json"
];

const AURORA_KP_URLS = (() => {
  const h = (window.location && window.location.hostname) ? window.location.hostname : "";
  const isLocal = (h === "localhost" || h === "127.0.0.1");
  return isLocal ? AURORA_KP_URLS_LOCAL : AURORA_KP_URLS_REMOTE;
})();
const AURORA_THROTTLE_MS = 90 * 1000;

  let auroraHooksInstalled = false;
  let auroraLastFetchAt = 0;
  let auroraLastKey = '';
  let auroraSelectedIdx = 0; // 0..48 (0 = jetzt)
  let auroraKpSeries = null; // array length 49
  let auroraWxSeries = null; // array length 49 {cloud, pp, pr}
  let auroraNow0 = 0;

// helper: update selection from any Aurora bar click (NOW or +48h)
function setAuroraSelectedIdx(i){
  const idx = Math.max(0, Math.min(48, Math.round(Number(i) || 0)));
  auroraSelectedIdx = idx;
  try{ renderAurora(); }catch(_){}
}


  function auroraQual(kp){
    if (!isFinite(kp)) return '—';
    if (kp >= 7) return 'sehr wahrscheinlich';
    if (kp >= 5) return 'wahrscheinlich';
    if (kp >= 4) return 'möglich';
    return 'gering';
  }

  function pad2(n){ return String(n).padStart(2,'0'); }
  function fmtClockUTC(ms){
    const d = new Date(ms);
    return pad2(d.getUTCHours()) + ':' + pad2(d.getUTCMinutes());
  }

  function clamp(v, a, b){ return Math.max(a, Math.min(b, v)); }

  
// Step11: Hybrid timeline under 48h plan (3h ticks + Keymarks: Sunrise/Sunset/00:00)
function fmtHHMM(d, tz){
  // Always show Iceland (Atlantic/Reykjavik) clock unless a different tz is explicitly passed.
  const useTz = tz || (typeof SUN_TZ === "string" ? SUN_TZ : "Atlantic/Reykjavik");
  try{
    return new Intl.DateTimeFormat("de-DE", {
      hour: "2-digit",
      minute: "2-digit",
      hour12: false,
      timeZone: useTz
    }).format(d);
  }catch(_){
    // Fallback: local time (should be rare)
    const h = String(d.getHours()).padStart(2,'0');
    const m = String(d.getMinutes()).padStart(2,'0');
    return `${h}:${m}`;
  }
}

// Aurora darkness model (photographer-friendly):
// Sun altitude >= -0.833° → day (0), <= -6° → night (1), smooth in-between.
function auroraDarknessFactorFromSunAlt(altDeg){
  const DAY_LIMIT = -0.833; // refraction-adjusted horizon
  const NIGHT_LIMIT = -6.0; // civil twilight end (practical)
  if (!isFinite(altDeg)) return 0;
  if (altDeg >= DAY_LIMIT) return 0;
  if (altDeg <= NIGHT_LIMIT) return 1;
  return (DAY_LIMIT - altDeg) / (DAY_LIMIT - NIGHT_LIMIT);
}

function auroraDarknessFactorUTC(lat, lon, dateUTC){
  const alt = sunCalcAltitudeDegUTC(lat, lon, dateUTC);
  return auroraDarknessFactorFromSunAlt(alt);
}


function renderAuroraTimeline48(baseMs, lat, lon){
  const el = document.getElementById('auroraTimeline48');
  if (!el) return;

  // Keep the baseline (first child), rebuild everything else
  while (el.children.length > 1) el.removeChild(el.lastChild);

  const hours = 49; // 0..48
  const W = 100;    // percent

  // 3h ticks (quiet)
// Photographer grid: hourly ticks, labels every 2 hours (quiet, but readable)
for (let h=0; h<=48; h+=1){
  const x = (h/48)*W;
  const t = new Date(baseMs + h*3600*1000);

  const tick = document.createElement('div');
  tick.style.position = 'absolute';
  tick.style.left = x.toFixed(3) + '%';
  tick.style.top = '18px';
  tick.style.width = '1px';
  tick.style.height = (h % 6 === 0) ? '14px' : (h % 2 === 0 ? '10px' : '6px');
  tick.style.background = (h % 6 === 0) ? 'rgba(255,255,255,.22)' : 'rgba(255,255,255,.14)';
  tick.style.transform = 'translateX(-0.5px)';
  el.appendChild(tick);

  if (h % 2 === 0){
    const lab = document.createElement('div');
    lab.textContent = fmtHHMM(t);
    lab.style.position = 'absolute';
    lab.style.left = x.toFixed(3) + '%';
    lab.style.top = '2px';
    lab.style.fontSize = '10px';
    lab.style.opacity = (h % 6 === 0) ? '.55' : '.38';
    lab.style.transform = 'translateX(-50%)';
    lab.style.whiteSpace = 'nowrap';
    el.appendChild(lab);
  }
}

// Step15: NOW night-window timeline (2h grid, photographer-friendly)
function renderAuroraNowTimeline2h(winStartMs, winEndMs){
  const el = document.getElementById('auroraNowTimeline2h');
  if (!el) return;

  // ---- Layout: timeline must live clearly *under* the bars (photographer-first) ----
  const wrap = document.getElementById('auroraNowWrap');
  if (wrap){
    // Give room for axis + labels
    wrap.style.height = '156px';
  }
  el.style.position = 'absolute';
  el.style.left = '0';
  el.style.right = '0';
  el.style.bottom = '0';
  el.style.height = '46px';
  el.style.marginTop = '0';
  el.style.opacity = '.95';
  el.style.pointerEvents = 'none';

    el.style.zIndex = '50';
// Keep baseline line (first child), rebuild everything else
  while (el.children.length > 1) el.removeChild(el.lastChild);

  const baseLine = el.children[0];
  if (baseLine){
    baseLine.style.top = '20px';
    baseLine.style.background = 'rgba(255,255,255,.16)';
  }

  const spanMs = Math.max(1, winEndMs - winStartMs);

  // Helper: minutes since midnight
  const minsOf = (d)=> d.getHours()*60 + d.getMinutes();

  // Photographer axis: ticks each hour, labels each hour (clear planning).
  const stepMin = 60;

  const start = new Date(winStartMs);
  const end   = new Date(winEndMs);

  // First tick: next full hour after start (real clock alignment)
  const first = new Date(start.getTime());
  first.setSeconds(0,0);
  if (first.getMinutes() !== 0) first.setMinutes(0,0,0);
  if (first.getTime() <= winStartMs) first.setHours(first.getHours() + 1);

  const mkTick = (xPct, isMajor)=>{
    const tick = document.createElement('div');
    tick.style.position = 'absolute';
    tick.style.left = xPct.toFixed(3) + '%';
    tick.style.top = '12px';
    tick.style.width = isMajor ? '3px' : '2px';
    tick.style.height = isMajor ? '18px' : '12px';
    tick.style.background = isMajor ? 'rgba(255,255,255,.48)' : 'rgba(255,255,255,.30)';
    tick.style.transform = 'translateX(-1px)';
    tick.style.borderRadius = '2px';
    tick.style.zIndex = '60';
    el.appendChild(tick);
  };

  const mkLabel = (xPct, txt, isMajor)=>{
    const lab = document.createElement('div');
    lab.textContent = txt;
    lab.style.position = 'absolute';
    lab.style.left = xPct.toFixed(3) + '%';
    lab.style.top = '30px';
    lab.style.fontSize = '11px';
        lab.style.color = 'rgba(255,255,255,.82)';
lab.style.opacity = isMajor ? '.82' : '.70';
    lab.style.transform = 'translateX(-50%)';
    lab.style.whiteSpace = 'nowrap';
    lab.style.pointerEvents = 'none';
    lab.style.zIndex = '60';
    el.appendChild(lab);
  };

  // Iterate hour-by-hour between start and end
  for (let t = first.getTime(); t <= winEndMs; t += stepMin*60*1000){
    const x = ((t - winStartMs) / spanMs) * 100;
    if (x < 0 || x > 100) continue;

    const d = new Date(t);
    // Major ticks every 2 hours (still label every hour, but give stronger rhythm)
    const isMajor = (minsOf(d) % 120) === 0;
    mkTick(x, isMajor);
    mkLabel(x, fmtHHMM(d), isMajor);
  }
}

// Step 17b: Photographer-first hour axis UNDER the NOW bars (so a KP spike has an instant clock time)
function renderAuroraNowHourAxis(winStartMs, winEndMs, barsEl){
  // RAW timeline: start at current window-start time (left) and run in 1h steps to the right.
  // Must survive refresh and be *visibly* under the NOW bars.
  if(!barsEl) return;

  const wrap = document.getElementById('auroraNowWrap') || (barsEl.closest ? barsEl.closest('#auroraNowWrap') : null);
  if(!wrap) return;

  // Make sure we have vertical room (bars + axis)
  wrap.style.height = '170px';
  wrap.style.overflow = 'visible';

  // Create / reuse axis container INSIDE the wrap (absolute bottom)
  let axisEl = document.getElementById('auroraNowHourAxis');
  if(!axisEl){
    axisEl = document.createElement('div');
    axisEl.id = 'auroraNowHourAxis';
    axisEl.style.position = 'absolute';
    axisEl.style.left = '0';
    axisEl.style.right = '0';
    axisEl.style.bottom = '6px';
    axisEl.style.height = '22px';
    axisEl.style.display = 'grid';
    axisEl.style.alignItems = 'end';
    axisEl.style.fontSize = '12px';
    axisEl.style.lineHeight = '1';
    axisEl.style.color = '#2f8cff'; // BLUE on purpose: debugging visibility
    axisEl.style.userSelect = 'none';
    axisEl.style.pointerEvents = 'none';
    axisEl.style.opacity = '0.98';
    axisEl.style.whiteSpace = 'nowrap';
    axisEl.style.zIndex = '60';
    axisEl.style.paddingTop = '6px';
    axisEl.style.borderTop = '1px solid rgba(255,255,255,.10)';
    wrap.appendChild(axisEl);
  }

  // Ensure bars don't overlap the axis (give them bottom space)
  barsEl.style.marginBottom = '30px';

  // Clear
  axisEl.innerHTML = '';

  if(!isFinite(winStartMs) || !isFinite(winEndMs) || winEndMs <= winStartMs) return;

  const spanMs = winEndMs - winStartMs;
  const hours = Math.max(1, Math.floor(spanMs / (3600*1000)));
  const cols = hours + 1; // include start and end ticks

  axisEl.style.gridTemplateColumns = `repeat(${cols}, 1fr)`;
  axisEl.style.gap = '0px';

  const fmt = (ms)=>{
    const d = new Date(ms);
    return String(d.getHours()).padStart(2,'0') + ':' + String(d.getMinutes()).padStart(2,'0');
  };

  for(let i=0;i<=hours;i++){
    const t = winStartMs + i*3600*1000;
    const lab = document.createElement('div');
    lab.textContent = fmt(t);
    lab.style.textAlign = (i===0) ? 'left' : (i===hours ? 'right' : 'center');
    lab.style.opacity = (i%2===0 || i===0 || i===hours) ? '0.98' : '0.72';
    axisEl.appendChild(lab);
  }
}





  // Keymarks styling
  const keyStyleTick = (d)=>{
    d.style.position = 'absolute';
    d.style.top = '12px';
    d.style.width = '2px';
    d.style.height = '20px';
    d.style.background = 'rgba(255,255,255,.70)';
    d.style.transform = 'translateX(-1px)';
    d.style.borderRadius = '2px';
  };
  const keyStyleLabel = (d)=>{
    d.style.position = 'absolute';
    d.style.top = '0px';
    d.style.fontSize = '11px';
    d.style.opacity = '.78';
    d.style.transform = 'translateX(-50%)';
    d.style.whiteSpace = 'nowrap';
  };

  // Midnight(s) in next 48h, local time
  try{
    const base = new Date(baseMs);
    const firstMid = new Date(base);
    firstMid.setHours(0,0,0,0);
    if (firstMid.getTime() <= baseMs) firstMid.setDate(firstMid.getDate()+1);
    for (let k=0;k<3;k++){
      const ms = firstMid.getTime() + k*24*3600*1000;
      const h = (ms - baseMs)/3600/1000;
      if (h >= 0 && h <= 48){
        const x = (h/48)*W;

        const tick = document.createElement('div');
        tick.style.left = x.toFixed(3) + '%';
        keyStyleTick(tick);
        el.appendChild(tick);

        const lab = document.createElement('div');
        lab.textContent = '00:00';
        lab.style.left = x.toFixed(3) + '%';
        keyStyleLabel(lab);
        el.appendChild(lab);
      }
    }
  }catch(_){}

  // Sunrise/Sunset: sun altitude threshold crossings
  const sunThresh = -0.833;
  if (isFinite(lat) && isFinite(lon) && typeof sunCalcAltitudeDegUTC === 'function'){
    try{
      const alts = [];
      for (let i=0;i<hours;i++){
        const dUTC = new Date(baseMs + i*3600*1000);
        alts.push(sunCalcAltitudeDegUTC(lat, lon, dUTC));
      }
      for (let i=0;i<hours-1;i++){
        const a0 = alts[i], a1 = alts[i+1];
        const s0 = (a0 <= sunThresh), s1 = (a1 <= sunThresh);
        if (s0 !== s1){
          const t = (sunThresh - a0) / (a1 - a0);
          const h = i + clamp(t,0,1);
          const x = (h/48)*W;

          const tick = document.createElement('div');
          tick.style.left = x.toFixed(3) + '%';
          keyStyleTick(tick);
          el.appendChild(tick);

          const lab = document.createElement('div');
          lab.textContent = (s0 === true && s1 === false) ? 'Sunrise' : 'Sunset';
          lab.style.left = x.toFixed(3) + '%';
          keyStyleLabel(lab);
          el.appendChild(lab);
        }
      }
    }catch(_){}
  }
}

function ensureAuroraUI(){
    if (document.getElementById('auroraBox')) return;

    const sunBox = document.getElementById('sunBox');
    const parent = sunBox ? sunBox.parentElement : document.getElementById('detail');
    if (!parent) return;

    const box = document.createElement('div');
    box.className = 'box';

    // Step4: match the visual 'card' language of other panels (minimal, tool-like)
    box.style.marginTop = '10px';
    box.style.padding = '10px';
    box.style.borderRadius = '10px';
    box.style.border = '1px solid rgba(255,255,255,0.08)';
    box.style.background = 'rgba(0,0,0,0.25)';
    box.style.color = 'inherit';
    box.id = 'auroraBox';
    box.setAttribute('data-panel-id', AURORA_PANEL_ID);
    box.setAttribute('data-panel-collapsible', '1');

    box.innerHTML = `
<div style="display:flex; align-items:center; justify-content:space-between; gap:10px;">
    <div style="font-weight:700;">Aurora (KP) &amp; Himmel</div>
    <div style="display:flex; align-items:center; gap:8px;">
      <div style="opacity:.65; font-size:12px;">Data: NOAA/SWPC + Open-Meteo</div>
      <button type="button" id="auroraToggleBtn" aria-expanded="true" aria-label="Panel ein-/ausklappen"
        style="border:1px solid rgba(255,255,255,.15); background:rgba(255,255,255,.06); color:inherit; border-radius:999px; padding:6px 10px; cursor:pointer; line-height:1;">
        ▾
      </button>
    </div>
  </div>

  <div id="auroraBody" style="margin-top:10px;">
    <div class="small-note">KP ist global (Geophysik). Sichtbar wird’s nur in Dunkelheit. Wolken/Regen sind standortbezogen.</div>

    <div style="margin-top:10px; opacity:.95; font-weight:700;">Jetzt – Nachtfenster</div>
    <div id="auroraNowMeta" style="opacity:.75; margin-top:4px; font-size:12px;">—</div>

    <div class="sun-graph-wrap aurora-graph-wrap" id="auroraNowWrap" style="margin-top:10px; position:relative; overflow:visible; height:170px;">
      <svg id="auroraNowSunSvg" viewBox="0 0 100 100" preserveAspectRatio="none" style="position:absolute;left:0;top:0;width:100%;height:100%;pointer-events:none;opacity:.55;">
        <path id="auroraNowSunPath" d="" fill="none" stroke="rgba(255,255,255,.22)" stroke-width="2" />
      </svg>
      <div class="aurora-bars" id="auroraNowBars"></div>
      <div class="aurora-marker" id="auroraNowMarker"></div>
      <div id="auroraNowTimeline2h" style="position:relative; height:34px; margin-top:6px; opacity:.92; pointer-events:none;">  <div style="position:absolute; left:0; right:0; top:14px; height:1px; background:rgba(255,255,255,.10);"></div></div>
<div id="auroraNowTimes" style="display:flex; justify-content:space-between; opacity:.8; margin-top:6px; font-size:12px;"></div>
      
    </div>

    <div id="auroraNowSel" style="margin-top:8px; opacity:.95;">Auswahl: —</div>

    <div style="margin-top:12px; display:flex; align-items:center; justify-content:space-between;">
      <div style="opacity:.95; font-weight:700;">Planung öffnen — +48h</div>
      <button type="button" id="auroraPlanToggle" aria-expanded="true" aria-label="48h ein-/ausklappen"
        style="border:1px solid rgba(255,255,255,.12); background:rgba(255,255,255,.04); color:inherit; border-radius:999px; padding:5px 10px; cursor:pointer; line-height:1;">
        ▾
      </button>
    </div>

    <div id="auroraPlanBody" style="margin-top:10px;">
      <div class="sun-graph-wrap aurora-graph-wrap" style="margin-top:10px; position:relative; overflow:hidden;">
        <svg id="auroraSunSvg" viewBox="0 0 100 100" preserveAspectRatio="none" style="position:absolute;left:0;top:0;width:100%;height:100%;pointer-events:none;opacity:.55;">
          <path id="auroraSunPath" d="" fill="none" stroke="rgba(255,255,255,.22)" stroke-width="2" />
        </svg>
        <div class="aurora-bars" id="auroraBars"></div>
        <div class="aurora-marker" id="auroraMarker"></div>
<div id="auroraTimeline48" style="position:absolute; left:10px; right:10px; bottom:2px; height:34px; opacity:.92; pointer-events:none; z-index:4;">
  <div style="position:absolute; left:0; right:0; top:22px; height:1px; background:rgba(255,255,255,.10);"></div>
</div>
<div id="auroraFeelingFooter" style="margin-top:10px; padding-top:8px; border-top:1px solid rgba(255,255,255,.08); opacity:.82;">
  <div id="auroraFeelingNow" style="margin-bottom:6px;"></div>
  <div id="auroraFeeling48"></div>
</div>


        <div class="aurora-end-labels" style="display:flex; justify-content:space-between; opacity:.8; margin-top:6px; font-size:12px;">
          <span>+0h</span><span>+48h</span>
        </div>
      </div>

      </div>

      <div id="auroraSel" style="margin-top:8px; opacity:.95;">Auswahl +0h: · KP — (—) · —% Wolken · —% Regenrisiko · Niederschlag: — mm</div>
    </div>
  </div>
`;
// Step4: collapse/expand (toggle on the right, like other boxes)
    const tBtn = box.querySelector('#auroraToggleBtn');
    const body = box.querySelector('#auroraBody');
    if (tBtn && body){
      tBtn.addEventListener('click', () => {
        const isOpen = body.style.display !== 'none';
        body.style.display = isOpen ? 'none' : '';
        tBtn.textContent = isOpen ? '▸' : '▾';
        tBtn.setAttribute('aria-expanded', isOpen ? 'false' : 'true');
      });
    }
// insert directly after sunBox (visual pairing)
    if (sunBox && sunBox.nextSibling){
      parent.insertBefore(box, sunBox.nextSibling);
    } else {
      parent.appendChild(box);
    }

    // Register in collapsible system (session-only)
    try{
      if (window.__DA_PANEL__ && window.__DA_PANEL__.register){
        window.__DA_PANEL__.register(box, AURORA_PANEL_ID, false);
      }
    }catch(_){}
  
// Step9: plan (+48h) collapse/expand (matches other boxes)
const pBtn = box.querySelector('#auroraPlanToggle');
const pBody = box.querySelector('#auroraPlanBody');
if (pBtn && pBody){
  pBtn.addEventListener('click', () => {
    const isOpen = pBody.style.display !== 'none';
    pBody.style.display = isOpen ? 'none' : '';
    pBtn.textContent = isOpen ? '▸' : '▾';
    pBtn.setAttribute('aria-expanded', isOpen ? 'false' : 'true');
  });
}

}

  function buildTicks(){
    const el = document.getElementById('auroraTicks');
    if (!el) return;
    // show every 6h as label – minimal
    const parts = [];
    for (let h=0; h<=48; h+=6){
      parts.push(`<span class="sun-hour" data-aurora-tick="${h}">+${h}h</span>`);
    }
    el.innerHTML = parts.join('');
  }

  function renderAurora(){
    const barsEl = document.getElementById('auroraBars');
    const selEl = document.getElementById('auroraSel') || document.getElementById('auroraSelection');
    const markerEl = document.getElementById('auroraMarker');
    if (!barsEl || !selEl || !markerEl) return;

    // Step3b: ensure predictable bar rendering (percent heights need explicit parent height)
    // Keep it minimal & tool-like: fixed strip height, bars grow in px.
    if (!barsEl.__auroraBarsInit){
      const wrap = barsEl.parentElement;
      if (wrap){
        wrap.style.position = 'relative';
        wrap.style.overflow = 'hidden';
      }
      barsEl.style.display = 'flex';
      barsEl.style.alignItems = 'flex-end';
      barsEl.style.gap = '2px';
      // a calm, readable strip – like a scale, not a light show
      barsEl.style.height = '120px';
      barsEl.style.padding = '12px 12px 18px 12px';
      markerEl.style.position = 'absolute';
      markerEl.style.top = '8px';
      markerEl.style.bottom = '18px';
      markerEl.style.width = '2px';
      markerEl.style.opacity = '.65';
      markerEl.style.background = 'rgba(255,255,255,.35)';
      markerEl.style.borderRadius = '2px';
      markerEl.style.pointerEvents = 'none';
      barsEl.__auroraBarsInit = true;
    }

    if (!auroraKpSeries || !auroraWxSeries){
      barsEl.innerHTML = '';
      selEl.textContent = 'Auswahl: —';
      return;
// Step13.2 (Hybrid, "flüstern" unten): Gefühl für aktuelle Nacht + 48h Planung
try{
  const cfAt = (i)=>{
    const wx = auroraWxSeries && auroraWxSeries[i] ? auroraWxSeries[i] : null;
    const cloud = (wx && wx.cloud != null && isFinite(wx.cloud)) ? Number(wx.cloud) : null;
    return (cloud == null) ? 1 : Math.max(0, Math.min(1, 1 - cloud/100));
  };

  // NOW-night feeling: take the best feeling within the current dark window (winStart..winEnd)
  let bestNowScore = -1;
  let bestNowIdx = winStart;
  for (let i=winStart; i<=winEnd; i++){
    const kp = auroraKpSeries[i];
    const score = computeAuroraFeeling(kp, darkF2[i], cfAt(i));
    if (score > bestNowScore){
      bestNowScore = score;
      bestNowIdx = i;
    }
  }

  // 48h feeling: best feeling within the next 48h where it's at least a bit dark
  let best48Score = -1;
  let best48Idx = 0;
  for (let i=0;i<=48;i++){
    const kp = auroraKpSeries[i];
    const score = computeAuroraFeeling(kp, darkF[i], cfAt(i));
    if (score > best48Score){
      best48Score = score;
      best48Idx = i;
    }
  }

  const kpNowBest = auroraKpSeries[bestNowIdx];
  const kp48Best = auroraKpSeries[best48Idx];

  renderAuroraFeelingLabeled('auroraFeelingNow', 'Jetzt (dunkel genug)', kpNowBest, darkF2[bestNowIdx], cfAt(bestNowIdx));
  renderAuroraFeelingLabeled('auroraFeeling48', '+48h (beste Phase)', kp48Best, darkF[best48Idx], cfAt(best48Idx));
}catch(_){}

    }

    const maxKP = 9;
    // Step5b: exaggerated, clearly readable KP bars (we'll dial back later)
const maxKP_BAR = 9;
const maxPx = 110;   // exaggerated on purpose
const minPx = 28;    // KP2 should be obvious
const gamma = 0.42;  // lifts low KP

function kpColor(kp){
  if (!isFinite(kp)) return "rgba(255,255,255,.18)";
  if (kp >= 5) return "rgba(180, 120, 255, .92)"; // >4 → purple
  if (kp >= 4) return "rgba(90, 255, 160, .92)";  // KP4 → green
  if (kp >= 2) return "rgba(255, 220, 80, .92)";  // KP2-3 → yellow
  return "rgba(90, 255, 160, .75)";               // KP0-1 → green low
}

// Build 0..48h (49 bars) from available KP points (nearest-by-hour)
const now = Date.now();
const hours = 49;

// Step9: NOW view = current dark window (for immediate decisions)
const nowBarsEl = document.getElementById('auroraNowBars');
const nowMarkerEl = document.getElementById('auroraNowMarker');
const nowTimesEl = document.getElementById('auroraNowTimes');
const nowMetaEl = document.getElementById('auroraNowMeta');

const pSun2 = (typeof window !== 'undefined' && window.__DA_SUN_PLAN_LAST_PAYLOAD__) ? window.__DA_SUN_PLAN_LAST_PAYLOAD__ : null;
const lat2 = isFinite(pSun2?.lat) ? Number(pSun2.lat) : (latInput ? parseFloat(latInput.value) : NaN);
const lon2 = isFinite(pSun2?.lon) ? Number(pSun2.lon) : (lonInput ? parseFloat(lonInput.value) : NaN);
const darkF2 = new Array(hours).fill(1);
const dark2 = new Array(hours).fill(true);
if (isFinite(lat2) && isFinite(lon2)){
  const base2 = Date.now();
  for (let i=0;i<hours;i++){
    const dUTC = new Date(base2 + i*3600*1000);
    const f = auroraDarknessFactorUTC(lat2, lon2, dUTC);
    darkF2[i] = f;
    dark2[i] = (f >= 0.05);
  }
}

let winStart = 0;
if (dark2[0] === false){
  let firstDark = -1;
  for (let i=0;i<hours;i++){ if (dark2[i] === true){ firstDark = i; break; } }
  if (firstDark >= 0) winStart = firstDark;
}
let winEnd = winStart;
while (winEnd+1 < hours && dark2[winEnd+1] === true) winEnd++;
if (winEnd - winStart > 12) winEnd = winStart + 12;

const nowCount = Math.max(1, winEnd - winStart + 1);
if (nowBarsEl){
        nowBarsEl.style.display = 'flex'; nowBarsEl.style.gap = '4px'; nowBarsEl.style.alignItems = 'flex-end'; nowBarsEl.style.height = '88px';

  nowBarsEl.textContent = '';
  for (let i=0;i<nowCount;i++){
    const el = document.createElement('div');
    el.style.flex = '1 1 0';
    el.style.borderRadius = '4px';
    el.style.cursor = 'pointer';
    nowBarsEl.appendChild(el);
  }
}
if (nowMarkerEl){
  nowMarkerEl.style.position = 'absolute';
  nowMarkerEl.style.top = '8px';
  nowMarkerEl.style.bottom = '18px';
  nowMarkerEl.style.width = '2px';
  nowMarkerEl.style.opacity = '.65';
  nowMarkerEl.style.background = 'rgba(255,255,255,.35)';
  nowMarkerEl.style.borderRadius = '2px';
  nowMarkerEl.style.pointerEvents = 'none';
}
// Step18 (Thomas): NOW timeline under the bars — starts at CURRENT time on every refresh (blue labels)
if (nowBarsEl){
  const wrapNow = document.getElementById('auroraNowWrap');
  if (wrapNow){
    let axisNow = document.getElementById('auroraNowHourAxisRow');
    if (!axisNow){
      axisNow = document.createElement('div');
      axisNow.id = 'auroraNowHourAxisRow';
      axisNow.style.marginTop = '8px';
      axisNow.style.paddingTop = '6px';
      axisNow.style.borderTop = '1px solid rgba(255,255,255,.10)';
      axisNow.style.display = 'grid';
      axisNow.style.gap = '4px';
      axisNow.style.alignItems = 'start';
      axisNow.style.fontSize = '12px';
      axisNow.style.lineHeight = '1';
      axisNow.style.color = 'rgba(80, 170, 255, .98)'; // blue, so you can't miss it
      axisNow.style.userSelect = 'none';
      axisNow.style.pointerEvents = 'none';
      axisNow.style.opacity = '.95';
      wrapNow.appendChild(axisNow);
    }
    axisNow.style.gridTemplateColumns = `repeat(${nowCount}, 1fr)`;
    axisNow.textContent = '';
    for (let i=0; i<nowCount; i++){
      const t = new Date(now + i*3600000);
      const lab = document.createElement('div');
      lab.textContent = fmtHHMM(t);
      lab.style.textAlign = 'center';
      lab.style.whiteSpace = 'nowrap';
      axisNow.appendChild(lab);
    }
  }
}

// NOW: hide grey edge-times (we keep the BLUE axis below as primary planning cue)
if (nowTimesEl){
  nowTimesEl.textContent = '';
  nowTimesEl.style.display = 'none';
}

// We still compute the NOW window start/end times for the 2h ticks helper
const __da_now_tStart = new Date(Date.now() + winStart*3600*1000);
const __da_now_tEnd   = new Date(Date.now() + winEnd*3600*1000);
try{ renderAuroraNowTimeline2h(__da_now_tStart.getTime(), __da_now_tEnd.getTime()); }catch(_){ }
if (nowMetaEl){
  nowMetaEl.textContent = (dark2[winStart] === true) ? `Dunkel: +${winStart}h bis +${winEnd}h` : `Kein Dunkelfenster in Sicht`;
}
// NOW: photographer hour-axis under the bars (hourly, starting at "now")
try{
  if (nowBarsEl && isFinite(winStart) && isFinite(winEnd)){
    const nowMs = Date.now();
    const tStartMs = nowMs + winStart*3600*1000;
    const tEndMs = nowMs + winEnd*3600*1000;
    renderAuroraNowHourAxis(tStartMs, tEndMs, nowBarsEl);
  }
}catch(_){ }



// NOW: draw inverse sun curve (variant B) inside the NOW window
try{
  const svgN = document.getElementById('auroraNowSunSvg');
  const pathN = document.getElementById('auroraNowSunPath');
  if (svgN && pathN && isFinite(lat2) && isFinite(lon2)){
    const pts = [];
    const base2 = Date.now();
    for (let j=0;j<nowCount;j++){
      const idx = winStart + j;
      const dUTC = new Date(base2 + idx*3600*1000);
      const alt = sunCalcAltitudeDegUTC(lat2, lon2, dUTC);
      const inv = auroraDarknessFactorFromSunAlt(alt);
      const x = (nowCount<=1) ? 0 : (j/(nowCount-1))*100;
      const y = 12 + inv*76;
      pts.push([x,y]);
    }
    let d = '';
    for (let i=0;i<pts.length;i++){
      d += (i===0 ? 'M' : 'L') + pts[i][0].toFixed(2) + ' ' + pts[i][1].toFixed(2) + ' ';
    }
    pathN.setAttribute('d', d.trim());
  }
}catch(_){}

const bars = [];
for (let i=0;i<hours;i++){
  const target = now + i*3600*1000;
  // nearest point in series
  let best = null;
  let bestD = Infinity;
  for (const p of auroraKpSeries){
    const d = Math.abs(p.ms - target);
    if (d < bestD){ bestD = d; best = p; }
  }
  bars.push(best ? best.kp : NaN);
}

barsEl.textContent = '';
for (let i=0;i<hours;i++){
  const kp = Number(bars[i]);
  const t = clamp((isFinite(kp) ? kp : 0) / maxKP_BAR, 0, 1);
  const hPx = (minPx + Math.pow(t, gamma) * (maxPx - minPx));

  const d = document.createElement('div');
  d.style.flex = '1 1 0';
  d.style.height = hPx + 'px';
  d.style.borderRadius = '4px';
  d.style.background = kpColor(kp);
  d.style.opacity = (i === auroraSelectedIdx) ? '1' : '.78';
  d.style.outline = (i === auroraSelectedIdx) ? '2px solid rgba(255,255,255,.55)' : '0';
  d.style.cursor = 'pointer';

  d.addEventListener('click', () => setAuroraSelectedIdx(i));
  barsEl.appendChild(d);
}

const n = auroraKpSeries.length; // 49
    const barW = 100 / n;

    const html = [];
    for (let i=0;i<n;i++){
      const kp = auroraKpSeries[i];
      const maxPx = 56;
      const minPx = 18;
      const t = clamp((kp / maxKP_BAR), 0, 1);
      const gamma = 0.55; // lift low KP a touch
      const hPx = Math.round(minPx + Math.pow(t, gamma) * (maxPx - minPx));
      const strong = (kp >= 5);
      const mild = (kp >= 4 && kp < 5);
      // minimal, aber "greifbar": neutral + Akzent bei relevant
      const bg = strong ? 'rgba(255,214,94,.85)' : mild ? 'rgba(255,214,94,.45)' : 'rgba(255,255,255,.18)';
      const glow = strong ? '0 0 10px rgba(255,214,94,.28)' : mild ? '0 0 8px rgba(255,214,94,.18)' : 'none';

      html.push(
        `<div class="aurora-bar" data-aurora-idx="${i}" title="+${i}h | KP ${isFinite(kp)?kp.toFixed(1):'—'}"
          style="flex:1 1 0; height:${hPx}px; background:${bg}; border-radius:2px; box-shadow:${glow}; opacity:${i===auroraSelectedIdx?1:0.85}; outline:${i===auroraSelectedIdx?'2px solid rgba(255,255,255,.28)':'none'}; outline-offset:0px;"></div>`
      );
    }
    barsEl.innerHTML = html.join('');

// highlight ticks (every 6h) to match selection
try{
  const tWrap = document.getElementById('auroraTicks');
  if (tWrap){
    const spans = tWrap.querySelectorAll('.sun-hour[data-aurora-tick]');
    spans.forEach(sp=>{
      const h = Number(sp.getAttribute('data-aurora-tick'));
      const active = (isFinite(h) && h === auroraSelectedIdx);
      sp.style.opacity = active ? '1' : '.75';
      sp.style.textDecoration = active ? 'underline' : 'none';
    });
  }
}catch(_){}

    // marker position
    const rect = barsEl.getBoundingClientRect();
    const wrapW = rect.width || 1;
    const padL = 10;
    const padR = 10;
    const usable = Math.max(1, wrapW - padL - padR);
    const x = padL + (usable * (auroraSelectedIdx / (n-1)));
    markerEl.style.left = x + 'px';

    // selection text
    const tMs = auroraNow0 + auroraSelectedIdx * 3600e3;
    const kp = auroraKpSeries[auroraSelectedIdx];
    const wx = auroraWxSeries[auroraSelectedIdx] || {};
    const cloud = (wx.cloud != null && isFinite(wx.cloud)) ? Math.round(wx.cloud) : null;
    const pp = (wx.pp != null && isFinite(wx.pp)) ? Math.round(wx.pp) : null;
    const pr = (wx.pr != null && isFinite(wx.pr)) ? wx.pr : null;

    const bits = [];
    bits.push(`Auswahl +${auroraSelectedIdx}h (${fmtClockUTC(tMs)}):`);
    bits.push(`KP ${isFinite(kp)?kp.toFixed(1):'—'} (${auroraQual(kp)})`);
    if (cloud != null) bits.push(`${cloud}% Wolken`);
    if (pp != null) bits.push(`${pp}% Regenrisiko`);
    if (pr != null && isFinite(pr)) bits.push(`Niederschlag: ${pr.toFixed(1)} mm`);
    selEl.textContent = bits.join(' · ');
  
  // Step5e: enforce visible KP bars + photographer colors (final pass, no console noise)
  try{
    if (barsEl && Array.isArray(auroraKpSeries) && auroraKpSeries.length){
      const hours = 49;

      const maxKP_BAR = 9;
      const maxPx = 140;   // tuned for visible decimal changes (not 'more drama')
      const minPx = 20;    // KP2 still obvious
      const gamma = 1.00;  // linear: decimals translate directly to pixels

      // Ensure exactly 49 bars exist
      if (!barsEl.children || barsEl.children.length !== hours){
        barsEl.textContent = '';
        for (let i=0;i<hours;i++){
          const d = document.createElement('div');
          d.style.flex = '1 1 0';
          d.style.borderRadius = '4px';
          d.style.cursor = 'pointer';
          d.addEventListener('click', () => setAuroraSelectedIdx(i));
          barsEl.appendChild(d);
        }
      }

      
// Step7: hide daylight – Aurora only makes sense in darkness.
// We keep the 48h window (planning) but visually suppress sunlit hours with a soft twilight fade.
const pSun = (typeof window !== 'undefined' && window.__DA_SUN_PLAN_LAST_PAYLOAD__) ? window.__DA_SUN_PLAN_LAST_PAYLOAD__ : null;
const latNow = isFinite(pSun?.lat) ? Number(pSun.lat) : (latInput ? parseFloat(latInput.value) : NaN);
const lonNow = isFinite(pSun?.lon) ? Number(pSun.lon) : (lonInput ? parseFloat(lonInput.value) : NaN);

const base = Date.now();
const darkF = new Array(hours).fill(1);
const dark  = new Array(hours).fill(true);

if (isFinite(latNow) && isFinite(lonNow)){
  for (let i=0;i<hours;i++){
    const dUTC = new Date(base + i*3600*1000);
    const f = auroraDarknessFactorUTC(latNow, lonNow, dUTC); // 0..1
    darkF[i] = f;
    dark[i]  = (f >= 0.05); // practical: almost day -> treat as day for snapping
  }

  // Inverse "darkness" curve: high = night, low = day (so sun vs aurora can "speak")
  try{
    const svg = document.getElementById('auroraSunSvg');
    const path = document.getElementById('auroraSunPath');
    if (svg && path){
      const pts = [];
      for (let i=0;i<hours;i++){
        const dUTC = new Date(base + i*3600*1000);
        const alt = sunCalcAltitudeDegUTC(latNow, lonNow, dUTC);
        const inv = auroraDarknessFactorFromSunAlt(alt); // 0..1 (day..night)
        const x = (i/(hours-1))*100;
        const y = 12 + inv*76;
        pts.push([x,y]);
      }
      let d = '';
      for (let i=0;i<pts.length;i++){
        d += (i===0 ? 'M' : 'L') + pts[i][0].toFixed(2) + ' ' + pts[i][1].toFixed(2) + ' ';
      }
      path.setAttribute('d', d.trim());
    }
  }catch(_){}
}

const kids = Array.from(barsEl.children || []);
// If current selection lands in daylight, snap to nearest dark hour (avoid confusing outputs)
if (dark[auroraSelectedIdx] === false){
  let best = -1, bestD = 1e9;
  for (let j=0;j<hours;j++){
    if (dark[j] === true){
      const d = Math.abs(j - auroraSelectedIdx);
      if (d < bestD){ bestD = d; best = j; }
    }
  }
  if (best >= 0) auroraSelectedIdx = best;
}

      for (let i=0;i<Math.min(hours, kids.length);i++){
        // auroraKpSeries in this app is already indexed 0..48 (numbers)
        const kp = Number(auroraKpSeries[i]);
        const t = clamp((isFinite(kp) ? kp : 0) / maxKP_BAR, 0, 1);
        const hPx = Math.round(minPx + Math.pow(t, gamma) * (maxPx - minPx));

        // Color mapping (as requested):
        // KP2-3 yellow, KP4 green, >4 purple. (KP0-1 low green)
        let col = "rgba(90, 255, 160, .75)";
        if (isFinite(kp)){
          if (kp > 4) col = "rgba(180, 120, 255, .92)";
          else if (kp >= 4) col = "rgba(90, 255, 160, .92)";
          else if (kp >= 2) col = "rgba(255, 220, 80, .92)";
          else col = "rgba(90, 255, 160, .75)";
        } else {
          col = "rgba(255,255,255,.14)";
        }

        const el = kids[i];
        // daylight suppression
        if (dark[i] === false){
          col = 'rgba(255,255,255,.07)';
        }

        const fDark = (typeof darkF !== 'undefined' && isFinite(darkF[i])) ? darkF[i] : (dark[i] ? 1 : 0);
        const baseH = hPx;
        const scaledH = 6 + (baseH - 6) * (0.15 + 0.85 * fDark);
        el.style.height = scaledH.toFixed(1) + 'px';
        // use !important to win against any existing CSS
        el.style.setProperty('background', col, 'important');
        el.style.setProperty('background-color', col, 'important');
        el.style.transition = 'height 260ms ease, background-color 260ms ease, outline-color 260ms ease';
        const fDark2 = (typeof darkF !== 'undefined' && isFinite(darkF[i])) ? darkF[i] : (dark[i] ? 1 : 0);
        const baseOp = (i === auroraSelectedIdx) ? 1 : 0.78;
        el.style.opacity = (0.22 + 0.78 * fDark2) * baseOp + '';
        el.style.outline = (i === auroraSelectedIdx) ? '2px solid rgba(255,255,255,.55)' : '0';
      }

// NOW bars styling (same mapping + height sensitivity)
try{
  if (nowBarsEl && nowBarsEl.children && nowBarsEl.children.length){
    const kidsN = Array.from(nowBarsEl.children);
    for (let j=0;j<kidsN.length;j++){
      const idx = winStart + j;
      const kp = Number(auroraKpSeries[idx]);
      const tN = clamp((isFinite(kp) ? kp : 0) / maxKP_BAR, 0, 1);
      const hN = (minPx + Math.pow(tN, gamma) * (maxPx - minPx));

      let colN = "rgba(90, 255, 160, .75)";
      if (isFinite(kp)){
        if (kp > 4) colN = "rgba(180, 120, 255, .92)";
        else if (kp >= 4) colN = "rgba(90, 255, 160, .92)";
        else if (kp >= 2) colN = "rgba(255, 220, 80, .92)";
        else colN = "rgba(90, 255, 160, .75)";
      } else {
        colN = "rgba(255,255,255,.14)";
      }

      const el = kidsN[j];
      const fDarkN = (typeof darkF2 !== 'undefined' && isFinite(darkF2[idx])) ? darkF2[idx] : (dark2[idx] ? 1 : 0);
      const scaledHN = 10 + (hN - 10) * (0.15 + 0.85 * fDarkN);
      el.style.height = scaledHN.toFixed(1) + 'px';
      el.style.setProperty('background', colN, 'important');
      el.style.setProperty('background-color', colN, 'important');
      el.style.opacity = (0.22 + 0.78 * ((typeof darkF2 !== 'undefined' && isFinite(darkF2[idx])) ? darkF2[idx] : 1)) + '';
      el.style.transition = 'height 260ms ease, background-color 260ms ease, outline-color 260ms ease';
      el.onclick = () => setAuroraSelectedIdx(idx);
    }

    if (nowMarkerEl){
      const sel = (auroraSelectedIdx >= winStart && auroraSelectedIdx <= winEnd) ? (auroraSelectedIdx - winStart) : 0;
      const pct = (kidsN.length <= 1) ? 0 : (sel / (kidsN.length-1));
      nowMarkerEl.style.left = (pct*100).toFixed(2) + '%';
    }
  }
}catch(_){}

    }
  }catch(e){
    // silent by design
  }
}

  async function fetchJson(url){
    const res = await fetch(url, { cache:'no-cache' });
    if (!res.ok) throw new Error('HTTP ' + res.status);
    return await res.json();
  }

  
  // Step5: bar color mapping for photographers (clear & immediate)
  function kpBarColor(kp){
    if (!isFinite(kp)) return "rgba(255,255,255,.18)";
    if (kp <= 1.999) return "rgba(60, 255, 140, .70)";       // KP0-1: green (low)
    if (kp <= 3.999) return "rgba(255, 220, 80, .80)";       // KP2-3: yellow (possible)
    if (kp <= 4.000) return "rgba(90, 255, 160, .85)";       // KP4: green (good)
    return "rgba(180, 120, 255, .85)";                       // >4: purple (strong)
  }

function parseKpSeries(js){
  // Accept both:
  //  1) Array of objects: [{time_tag, kp_index}, ...]
  //  2) NOAA SWPC "products" format: [ [header...], [row...], ... ]
  if (!Array.isArray(js)) return [];

  // NOAA "products" format → convert to object rows
  if (js.length && Array.isArray(js[0])){
    const header = js[0].map(h => String(h || "").trim());
    const rows = [];
    for (let i=1;i<js.length;i++){
      const arr = js[i];
      if (!Array.isArray(arr)) continue;
      const obj = {};
      for (let c=0;c<header.length;c++){
        obj[header[c]] = arr[c];
      }
      rows.push(obj);
    }
    js = rows;
  }

  const out = [];
  for (const r of js){
    if (!r || typeof r !== 'object') continue;

    // common SWPC keys: time_tag, kp_index; sometimes "Kp" or "kp"
    const t = r.time_tag || r.time || r.datetime || r.date || r["time-tag"] || r["Time"] || null;

    // kp can be under various keys depending on product
    const kp =
      (r.kp_index != null) ? r.kp_index :
      (r.kp != null) ? r.kp :
      (r.Kp != null) ? r.Kp :
      (r.value != null) ? r.value :
      (r["kp-index"] != null) ? r["kp-index"] :
      null;

    const ms = t ? Date.parse(String(t)) : NaN;
    const kpf = (kp != null) ? Number(kp) : NaN;
    if (isFinite(ms) && isFinite(kpf)) out.push({ ms, kp:kpf });
  }
  out.sort((a,b)=>a.ms-b.ms);
  return out;
}

  function kpAt(ms, rows){
    if (!rows || !rows.length) return NaN;
    // last <= ms
    let lo = 0, hi = rows.length - 1;
    if (ms < rows[0].ms) return rows[0].kp;
    if (ms >= rows[hi].ms) return rows[hi].kp;
    // binary search for rightmost <= ms
    while (lo <= hi){
      const mid = (lo + hi) >> 1;
      if (rows[mid].ms <= ms){ lo = mid + 1; }
      else { hi = mid - 1; }
    }
    return rows[Math.max(0, lo-1)].kp;
  }

  function buildWx48(hourlyNorm, now0){
    const out = new Array(49).fill(null).map(()=>({cloud:null, pp:null, pr:null}));
    if (!hourlyNorm || !hourlyNorm.length) return out;

    // create map by hour ms (rounded)
    const map = new Map();
    for (const r of hourlyNorm){
      const ms = Date.parse(r.time);
      if (!isFinite(ms)) continue;
      const key = Math.round(ms/3600e3); // hour index
      map.set(key, r);
    }

    for (let i=0;i<=48;i++){
      const ms = now0 + i*3600e3;
      const key = Math.round(ms/3600e3);
      const r = map.get(key);
      if (!r) continue;
      out[i] = { cloud:r.cloud, pp:r.precipProb, pr:r.precip };
    }
    return out;
  }

  async function auroraUpdate(lat, lon, force=false){
    try{
      ensureAuroraUI();
      buildTicks();

      const now = Date.now();
      const key = `${lat.toFixed(3)},${lon.toFixed(3)}`;
      if (!force){
        if (now - auroraLastFetchAt < AURORA_THROTTLE_MS) return;
        if (key === auroraLastKey && now - auroraLastFetchAt < (AURORA_THROTTLE_MS*2)) return;
      }
      auroraLastFetchAt = now;
      auroraLastKey = key;

      // anchor: exact now (UTC) for +0..+48
      auroraNow0 = now;

      // 1) KP from NOAA (global)
      let kpRows = [];
      for (const url of AURORA_KP_URLS){
        try{
          const js = await fetchJson(url);
          kpRows = parseKpSeries(js);
          if (kpRows.length) break;
        }catch(_){}
      }

      const kpSeries = [];
      for (let i=0;i<=48;i++){
        const ms = auroraNow0 + i*3600e3;
        kpSeries.push(kpAt(ms, kpRows));
      }
      auroraKpSeries = kpSeries;

      // 2) Wolken/Regen vom Standort (Open-Meteo Hourly)
      let hourly = null;
      try{
        if (typeof sunFetchHourly === 'function'){
          hourly = await sunFetchHourly(lat, lon, 'UTC');
        }
      }catch(_){}
      let norm = [];
      try{
        if (typeof sunNormalizeHourly === 'function'){
          norm = sunNormalizeHourly(hourly);
        }
      }catch(_){}
      auroraWxSeries = buildWx48(norm, auroraNow0);

      // clamp selected to range (in case)
      auroraSelectedIdx = clamp(auroraSelectedIdx, 0, 48);

      renderAurora();
    }catch(_){
      // leise bleiben – Aurora ist Zusatz
    }
  }

  function installHooks(){
    if (auroraHooksInstalled) return;

    // click selection on bars
    document.addEventListener('click', function(ev){
      const b = ev.target && ev.target.closest ? ev.target.closest('.aurora-bar[data-aurora-idx]') : null;
      if (!b) return;
      const idx = Number(b.getAttribute('data-aurora-idx'));
      if (!isFinite(idx)) return;
      auroraSelectedIdx = clamp(idx, 0, 48);
      try{ renderAurora(); }catch(_){}
    });

// click selection on 6h ticks
document.addEventListener('click', function(ev){
  const t = ev.target && ev.target.closest ? ev.target.closest('.sun-hour[data-aurora-tick]') : null;
  if (!t) return;
  const h = Number(t.getAttribute('data-aurora-tick'));
  if (!isFinite(h)) return;
  auroraSelectedIdx = clamp(h, 0, 48);
  try{ renderAurora(); }catch(_){}
});

    // updateMap hook (GPS/manual/programmatic)
    try{
      if (typeof updateMap === 'function' && !updateMap.__auroraWrapped){
        const _u = updateMap;
        const wrapped = function(lat, lon, accuracyMeters=null){
          const r = _u(lat, lon, accuracyMeters);
          try{ auroraUpdate(lat, lon, true); }catch(_){}
          return r;
        };
        wrapped.__auroraWrapped = true;
        updateMap = wrapped;
      }
    }catch(_){}

    // marker hooks (if available)
    const w = setInterval(()=>{
      try{
        if (typeof marker !== 'undefined' && marker){
          try{
            const onMove = () => { try{ const p = marker.getLatLng(); auroraUpdate(p.lat, p.lng, false);}catch(_){} };
            try{ marker.on('dragend', onMove); }catch(_){}
            try{ marker.on('drag', onMove); }catch(_){}
            // initial
            try{ const p = marker.getLatLng(); auroraUpdate(p.lat, p.lng, true);}catch(_){}
          }catch(_){}
          clearInterval(w);
        }
      }catch(_){}
    }, 250);

    auroraHooksInstalled = true;
  }

  document.addEventListener('DOMContentLoaded', function(){
    try{ ensureAuroraUI(); buildTicks(); }catch(_){}
    try{ installHooks(); }catch(_){}
  });

})();


/* pad */


// ===============================
// STEP 13 – Aurora Feeling Hybrid
// ===============================

function computeAuroraFeeling(kp, darknessFactor, cloudFactor){
    const kpScore = Math.min(kp / 5, 1);
    const darkScore = Math.max(0, Math.min(darknessFactor, 1));
    const cloudScore = Math.max(0, Math.min(cloudFactor, 1));

    const total =
        kpScore * 0.5 +
        darkScore * 0.3 +
        cloudScore * 0.2;

    return total * 100;
}

function feelingText(score){
    if(score < 20) return "sehr ruhig";
    if(score < 40) return "ruhig";
    if(score < 60) return "ruhig → aktiv";
    if(score < 75) return "aktiv";
    if(score < 90) return "aktiv → intensiv";
    return "magisch";
}

function feelingBar(score){
    const filled = Math.round(score / 10);
    return "■".repeat(filled) + "□".repeat(10-filled);
}

function renderAuroraFeeling(containerId, kp, darknessFactor, cloudFactor){
    const el = document.getElementById(containerId);
    if(!el) return;

    const score = computeAuroraFeeling(kp, darknessFactor, cloudFactor);

    el.innerHTML = `
        <div style="margin-top:6px; font-size:13px; opacity:.9">
            Aurora Gefühl: ${feelingText(score)}
        </div>
        <div style="font-size:14px; letter-spacing:1px; opacity:.75">
            ${feelingBar(score)}
        </div>
    `;
}
function renderAuroraFeelingLabeled(containerId, label, kp, darknessFactor, cloudFactor){
    const el = document.getElementById(containerId);
    if(!el) return;

    const score = computeAuroraFeeling(kp, darknessFactor, cloudFactor);
    const txt = feelingText(score);
    const bar = feelingBar(score);

    el.innerHTML = `
        <div style="font-size:12px; opacity:.70; margin-bottom:2px">${label}: ${txt}</div>
        <div style="font-size:13px; letter-spacing:1px; opacity:.62">${bar}</div>
    `;
}


// ===============================
// STEP 13 – Aurora State (clean)
// ===============================
function ensureAuroraState(){
  if(!window.__auroraState) window.__auroraState = {};
  return window.__auroraState;
}

function updateAuroraState(payload){
  const s = ensureAuroraState();
  s.nightWindow = payload.nightWindow || null;
  s.series = payload.series || null;
  s.meta = payload.meta || null;
  return s;
}

function renderAuroraFeelingFromState(){
  try{
    const s = ensureAuroraState();
    const nw = s.nightWindow;
    const ser = s.series;
    if(!nw || !ser) return;

    const kpArr = ser.kp;
    const dark48 = ser.dark48;
    const darkNow = ser.darkNow;
    const wxArr = ser.wx;

    const cloudFactor = (i)=>{
      const wx = wxArr && wxArr[i] ? wxArr[i] : null;
      const cloud = (wx && wx.cloud != null && isFinite(wx.cloud)) ? Number(wx.cloud) : null;
      return (cloud == null) ? 1 : Math.max(0, Math.min(1, 1 - cloud/100));
    };

    // best NOW (within night window indices)
    let bestNowScore = -1;
    let bestNowIdx = nw.startIdx;
    for(let i=nw.startIdx; i<=nw.endIdx; i++){
      const score = computeAuroraFeeling(kpArr[i], darkNow[i], cloudFactor(i));
      if(score > bestNowScore){
        bestNowScore = score;
        bestNowIdx = i;
      }
    }

    // best 48h (0..48)
    let best48Score = -1;
    let best48Idx = 0;
    for(let i=0;i<=48;i++){
      const score = computeAuroraFeeling(kpArr[i], dark48[i], cloudFactor(i));
      if(score > best48Score){
        best48Score = score;
        best48Idx = i;
      }
    }

    if(typeof renderAuroraFeelingLabeled === "function"){
      renderAuroraFeelingLabeled(
        "auroraFeelingNow",
        "Heute Nacht (beste Phase)",
        kpArr[bestNowIdx],
        darkNow[bestNowIdx],
        cloudFactor(bestNowIdx)
      );

      renderAuroraFeelingLabeled(
        "auroraFeeling48",
        "+48h (beste Phase)",
        kpArr[best48Idx],
        dark48[best48Idx],
        cloudFactor(best48Idx)
      );
    }
  }catch(_){
    // Konsole muss sauber bleiben: silent
  }
}







// Step16b: hour axis under bars
