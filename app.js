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
  if (coordsEl) coordsEl.textContent = `Koordinaten: ${fmt(lat)}, ${fmt(lon)}`;
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
// FOTOGRAFISCHE SPOTS – Südküste (Reykjavík → Höfn)
// Sichtbarkeit: erst ab bestimmtem Zoom, dezent als CircleMarker
// =============================

const SPOT_MIN_ZOOM = 0; // immer sichtbar (ohne Klick)

const PHOTO_SPOTS = [
  {
    id: "reykjanes_transition",
    lat: 63.9000, lon: -22.2500,
    cat: "Küste & Struktur",
    text: "Übergänge von Siedlung zu Lava erzeugen klare Kontraste und grafische Brüche. Aus der Luft werden Linien und Maßstäbe sichtbar, die vom Boden oft verloren gehen. Wirkt besonders gut bei ruhigen Bedingungen."
  },
  {
    id: "thjorsa_plain",
    lat: 63.7833, lon: -20.8000,
    cat: "Maßstab & Weite",
    text: "Weite Ebenen und Flussläufe ergeben ruhige, lange Kompositionen. Ideal, wenn man Isolation und Größenverhältnisse zeigen will, statt einzelne Motive. Bei tiefer Sonne entstehen starke Schattenkanten."
  },
  {
    id: "seljalands_area",
    lat: 63.6170, lon: -19.9833,
    cat: "Struktur & Bewegung",
    text: "Nicht der Wasserfall, sondern das Umfeld: Wasseradern, Feuchtflächen und Linien im Gelände. Aus der Luft wird sichtbar, wie Wasser die Landschaft schreibt. Bei Böen eher vorsichtig, hier ist Turbulenz möglich."
  },
  {
    id: "skogasandur_minimal",
    lat: 63.4833, lon: -19.4833,
    cat: "Struktur & Grafik",
    text: "Schwarze Ebenen, Texturen und feine Spuren – minimalistisch, grafisch, sehr „Island“. Der Reiz liegt im Reduzieren, nicht im Spektakel. Funktioniert gut, wenn das Licht seitlich kommt."
  },
  {
    id: "solheimasandur_outwash",
    lat: 63.4595, lon: -19.3646,
    cat: "Struktur & Bewegung",
    text: "Verzweigte Wasserläufe und wechselnde Sandstrukturen – Ordnung im Chaos. Aus der Luft entstehen natürliche Muster, die sich je nach Wetter und Jahreszeit verändern. Böen entscheiden hier oft über Go/No-Go."
  },
  {
    id: "dyrholaey_rhythm",
    lat: 63.4022, lon: -19.1307,
    cat: "Küste & Linien",
    text: "Küstenverlauf, Brandung und Rhythmus – starke Linienführung, klare Richtung. Aus der Luft wirken Wiederholungen und Übergänge besonders intensiv. Bitte sensibel: Natur und Besucherströme im Blick behalten."
  },
  {
    id: "myrdalssandur_weite",
    lat: 63.4579, lon: -18.5581,
    cat: "Maßstab & Weite",
    text: "Große Flächen, wenig Ablenkung – ideal für Bilder, die Größe und Leere transportieren. Hier kann man mit Höhe und Perspektive sehr fein dosieren. Bei Wind fühlt sich die Weite schnell „hart“ an."
  },
  {
    id: "skeidararsandur_dynamics",
    lat: 63.9000, lon: -17.2333,
    cat: "Bewegung & Struktur",
    text: "Schwemmland in XXL: verzweigte Flussarme, ständig wechselnde Muster, sichtbare Dynamik. Aus der Luft wird die Landschaft zur Karte. Sehr lohnend – und zugleich ein Spot, an dem Böen ernst zu nehmen sind."
  },
  {
    id: "skaftafell_tongues",
    lat: 64.0147, lon: -16.9739,
    cat: "Maßstab & Linien",
    text: "Übergang von Eis zu Erde: Kanten, Risse, Richtungen. Aus der Luft entsteht ein starkes Gefühl von Gewicht und Bewegung im Stillstand. Bei klarer Sicht wirken Strukturen im Eis besonders plastisch."
  },
  {
    id: "jokulsarlon_outflow",
    lat: 64.0784, lon: -16.2306,
    cat: "Textur & Fluss",
    text: "Abfluss, Strömung und Textur – hier sieht man, wie das Wasser die Formen zieht. Aus der Luft ergeben sich ruhige, grafische Bilder mit hohem Detailreichtum. Licht und Wind bestimmen, ob es „glatt“ oder „wild“ wird."
  },
  {
    id: "hofn_foreland",
    lat: 64.2539, lon: -15.2121,
    cat: "Weite & Ruhe",
    text: "Küstennahe Ebenen und Lagunenbereiche – ein leiser Abschluss nach der Strecke. Aus der Luft wirken Übergänge zwischen Land, Wasser und Sand sehr klar. Ideal, wenn man Ruhe und Raum erzählen will."
  }
];

let _photoSpotLayer = null;
let _photoSpotsOnMap = false;

function _spotPopupHTML(spot) {
  const safe = (s) => String(s).replace(/[&<>"]/g, (c) => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
  return `
    <div style="font-family:system-ui, -apple-system, Segoe UI, Roboto, Arial; max-width:260px">
      <div style="font-weight:700; margin-bottom:4px;">Fotografischer Spot</div>
      <div style="opacity:.85; margin-bottom:6px;"><i>${safe(spot.cat)}</i></div>
      <div style="line-height:1.35;">${safe(spot.text)}</div>
      <div style="margin-top:8px; font-size:12px; opacity:.7;">
        Hinweis: Inspiration, keine Flugfreigabe. Recht/Wind bitte separat prüfen.
      </div>
    </div>
  `;
}

function _ensurePhotoSpots() {
  if (_photoSpotLayer) return;

  _photoSpotLayer = L.layerGroup();

  for (const s of PHOTO_SPOTS) {
    // Spot-Typen (abwärtskompatibel):
    // - "drone" (Drohnen-Spot) -> dunkles, sattes Blau
    // - sonst -> dunkles, sattes Violett (Fotografie)
    const _tRaw = (s.type || s.kind || s.mode || "").toString().toLowerCase();
    const _isDrone = _tRaw.includes("drone") || _tRaw.includes("uav") || _tRaw.includes("drohne");
    const _style = _isDrone
      ? {
          radius: 9,
          weight: 3,
          opacity: 0.98,
          color: "#0A2A66",
          fillColor: "#123B8A",
          fillOpacity: 0.88
        }
      : {
          radius: 9,
          weight: 3,
          opacity: 0.98,
          color: "#3B145F",
          fillColor: "#5A1D8A",
          fillOpacity: 0.88
        };

    const m = L.circleMarker([s.lat, s.lon], _style);
    m.bindPopup(_spotPopupHTML(s));
    _photoSpotLayer.addLayer(m);
  }
}

function _updatePhotoSpotVisibility() {
  if (!map) return;
  _ensurePhotoSpots();

  const z = map.getZoom();
  const shouldShow = z >= SPOT_MIN_ZOOM;

  if (shouldShow && !_photoSpotsOnMap) {
    _photoSpotLayer.addTo(map);
    _photoSpotsOnMap = true;
  } else if (!shouldShow && _photoSpotsOnMap) {
    map.removeLayer(_photoSpotLayer);
    _photoSpotsOnMap = false;
  }
}

// Hook nach Map-Init
try {
  _updatePhotoSpotVisibility();
  map.on("zoomend", _updatePhotoSpotVisibility);
} catch (e) {
  // falls map noch nicht existiert, später versuchen
  const _spotTimer = setInterval(() => {
    try {
      if (typeof map !== "undefined" && map && typeof map.getZoom === "function") {
        _updatePhotoSpotVisibility();
        map.on("zoomend", _updatePhotoSpotVisibility);
        clearInterval(_spotTimer);
      }
    } catch (_) {}
  }, 250);
}
