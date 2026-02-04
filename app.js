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

  L.tileLayer("https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png", {
    maxZoom: 19,
    noWrap: true,
    bounds: getIcelandBounds(),
    attribution: "&copy; OpenStreetMap contributors",
  }).addTo(map);

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
  box.style.marginTop = "10px";
  box.style.padding = "10px";
  box.style.borderRadius = "10px";
  box.style.border = "1px solid rgba(255,255,255,0.08)";
  box.style.background = "rgba(0,0,0,0.25)";
  box.style.color = "inherit";

  box.innerHTML = `
    <div style="font-weight:700;margin-bottom:6px;">Wind am Standort</div>
    <div id="windValues" style="opacity:.95;">—</div>
    <div id="windDJI" style="margin-top:6px;opacity:.95;">—</div>
    <div style="margin-top:6px;opacity:.65;font-size:12px;line-height:1.25;">
      Einschätzung basiert auf DJI-Referenzwerten (konservativ) & Modellwind (10 m). Lokale Effekte möglich.
    </div>
  `;

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
  box.style.marginTop = "10px";
  box.style.padding = "10px";
  box.style.borderRadius = "10px";
  box.style.border = "1px solid rgba(255,255,255,0.08)";
  box.style.background = "rgba(0,0,0,0.25)";
  box.style.color = "inherit";

  box.innerHTML = `
    <div style="display:flex; align-items:flex-start; justify-content:space-between; gap:10px;">
      <div>
        <div style="font-weight:700;">IMO – Now & Next</div>
        <div style="opacity:.65; font-size:12px; margin-top:2px;">Icelandic Meteorological Office (offizieller Wetterdienst Islands)</div>
      </div>
      <div style="opacity:.65; font-size:12px; white-space:nowrap;">Data: IMO / vedur.is</div>
    </div>

    <div style="margin-top:6px; opacity:.9; font-size:13px; line-height:1.35;">
      <div id="imoNow" style="margin-top:4px;">—</div>
      <div id="imoNext" style="margin-top:6px;">—</div>
      <div id="imoAlerts" style="margin-top:8px;">—</div>
    </div>

    <div style="margin-top:8px; opacity:.65; font-size:12px; line-height:1.25;">
      Alle Werte stammen von automatischen IMO-Messstationen (AWS). ‚—‘ bedeutet: Sensor nicht vorhanden oder aktuell keine Daten.<br/>
      NOW = nächste Messstation(en) (AWS). NEXT = Kurztrend aus den letzten ~60 Minuten (kein Modell).
    </div>
  `;

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
    const slat = s?.lat ?? s?.latitude;
    const slon = s?.lon ?? s?.longitude;
    if (typeof slat !== "number" || typeof slon !== "number") continue;
    const dist = imoHaversineKm(lat, lon, slat, slon);
    arr.push({ station: s, distKm: dist });
  }
  arr.sort((a,b) => a.distKm - b.distKm);
  return arr.slice(0, n);
}

async function imoFetchLatest10min(stationIds) {
  const params = new URLSearchParams();
  for (const id of stationIds) params.append("station_id", String(id));
  params.set("fields", "basic"); // genügt für Apps/Dashboards laut API
  const url = `${IMO_WEATHER_BASE}/observations/aws/10min/latest?${params.toString()}`;
  const res = await fetch(url, { cache: "no-cache" });
  if (!res.ok) throw new Error(`IMO aws latest HTTP ${res.status}`);
  const data = await res.json();
  return Array.isArray(data) ? data : [];
}

async function imoFetchRecent10min(stationId, count = 6) {
  // letzte ~60 min (6×10min), DESC
  const params = new URLSearchParams();
  params.append("station_id", String(stationId));
  params.set("fields", "basic");
  params.set("count", String(count));
  params.set("order", "desc");
  const url = `${IMO_WEATHER_BASE}/observations/aws/10min?${params.toString()}`;
  const res = await fetch(url, { cache: "no-cache" });
  if (!res.ok) throw new Error(`IMO aws series HTTP ${res.status}`);
  const data = await res.json();
  return Array.isArray(data) ? data : [];
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
    const sid = s?.id ?? s?.station_id;
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
    const ids = nearest.map(x => x.station?.id ?? x.station?.station_id).filter(x => x !== undefined && x !== null);
    const latest = await imoFetchLatest10min(ids.map(Number));
    const latestByStationId = new Map();
    for (const o of latest) {
      const sid = o?.station_id ?? o?.id ?? o?.station;
      if (sid !== undefined && sid !== null) latestByStationId.set(String(sid), o);
    }

    // 3) Series für die nächste Station (Trend ~60 min)
    let seriesMain = [];
    if (ids.length) {
      seriesMain = await imoFetchRecent10min(Number(ids[0]), 6);
    }

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
  box.style.marginTop = "10px";
  box.style.padding = "10px";
  box.style.borderRadius = "10px";
  box.style.border = "1px solid rgba(255,255,255,0.08)";
  box.style.background = "rgba(0,0,0,0.25)";
  box.style.color = "inherit";

  box.innerHTML = `
    <div style="display:flex; align-items:center; justify-content:space-between; gap:10px;">
      <div style="font-weight:800;">Spot-Modus</div>
      <div id="spotPill" style="padding:4px 10px; border-radius:999px; font-size:12px; border:1px solid rgba(255,255,255,0.12); opacity:.9;">
        —
      </div>
    </div>

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
  `;

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
