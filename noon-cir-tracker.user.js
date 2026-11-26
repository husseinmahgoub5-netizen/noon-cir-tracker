// ==UserScript==
// @name         noon CIR Pickup Tracker (bulk)
// @namespace    https://express-control.noon.team/
// @version      1.0.0
// @description  Paste many CIRs and get the state of each one with a single report query (cir_pickup_tracker)
// @author       husseinmahgoub5-netizen
// @homepageURL  https://github.com/husseinmahgoub5-netizen/noon-cir-tracker
// @updateURL    https://raw.githubusercontent.com/husseinmahgoub5-netizen/noon-cir-tracker/main/noon-cir-tracker.user.js
// @downloadURL  https://raw.githubusercontent.com/husseinmahgoub5-netizen/noon-cir-tracker/main/noon-cir-tracker.user.js
// @match        https://express-control.noon.team/*
// @run-at       document-idle
// @grant        none
// ==/UserScript==
(function () {
  'use strict';
  if (window.__nctLoaded) return;
  window.__nctLoaded = true;

  var TAG = '[noon-cir-tracker]';
  var PAGE_CODE = 'cir_pickup_tracker';
  var CARD_ID = 'nct-card';
  var STYLE_ID = 'nct-style';
  var LS_KEY = 'noonCirTracker.v1';
  var BATCH_SIZE = 30;
  var QUIET_MS = 350;
  var BATCH_MAX_MS = 15000;
  var SINGLE_MAX_MS = 10000;
  var NO_ACTIVITY_MS = 3000;
  var FALLBACK_MAX = 40;
  var GAP_MS = 60;
  var MAX_EVENTS = 60;
  var MAX_REFS = 5000;
  var LEG_URL = '/_svc/express-api-v1/control/search/creq-leg';
  var LOOKUP_MAX = 5000, LEG_START = 8, LEG_MIN = 2, LEG_MAX = 12; // creq-leg concurrency: adaptive (halves on 429, creeps back up)

  var STATES = ['picked', 'assigned', 'attempted', 'preassigned', 'notassigned', 'held', 'canceled', 'tpl', 'nodata'];
  var LABEL = { picked: 'Picked', assigned: 'Assigned (no attempt)', attempted: 'Attempted', preassigned: 'Pre-assigned', notassigned: 'Not assigned', held: 'Held', canceled: 'Canceled', tpl: 'TPL', nodata: '-', pending: 'Checking...' };
  var COLOR = { picked: '#d6f5d6', assigned: '#fff4bf', attempted: '#ffd9b0', preassigned: '#d3f4f1', notassigned: '#cdeafd', held: '#e7ddf8', canceled: '#ffdbe5', tpl: '#e7ddf8', nodata: '#eceef2', pending: '#f5f6fa' };

  function log() { try { console.log.apply(console, [TAG].concat([].slice.call(arguments))); } catch (e) {} }
  function err() { try { console.error.apply(console, [TAG].concat([].slice.call(arguments))); } catch (e) {} }
  function now() { return performance.now(); }
  function sleep(ms) { return new Promise(function (r) { setTimeout(r, ms); }); }

  /* ---------------- helpers ---------------- */
  function normState(raw) {
    if (raw == null) return null;
    var s = String(raw).toLowerCase().replace(/[^a-z0-9]+/g, '_');
    if (/cancel|cancelled|rejected/.test(s)) return 'canceled';
    if (/picked|pick_up_done|shipment_picked/.test(s)) return 'picked';
    if (/pre_?assigned/.test(s)) return 'preassigned';
    if (/not_?assigned|unassigned/.test(s)) return 'notassigned';
    if (/assigned.*not.*attempted|not_attempted/.test(s)) return 'assigned';
    if (/assigned/.test(s)) return 'assigned';
    return null;
  }
  function str(v) { return v == null ? '' : String(v).trim(); }
  function refKey(s) { var p = String(s).split('::'); return p[p.length - 1].trim().toLowerCase(); }
  function refLast(s) { var p = String(s).split('::'); return p[p.length - 1].trim(); }
  function utcMode() {
    try {
      var bs = [].slice.call(document.querySelectorAll('[role="group"] button'));
      var u = bs.filter(function (b) { return /^\s*utc time\s*$/i.test(b.textContent); })[0];
      return !!u && /MuiButton-contained/.test(u.className);
    } catch (e) { return false; }
  }
  function parseTs(v) {
    // API timestamps carry no timezone and are UTC (the page shows them converted to the browser zone)
    if (v == null || v === '') return 0;
    if (typeof v === 'number') return v < 1e12 ? v * 1000 : v;
    var s = String(v).trim();
    if (/^\d+$/.test(s)) { var n = +s; return n < 1e12 ? n * 1000 : n; }
    var m = s.match(/^(.*\S)\s+(UTC|GMT|[A-Za-z]+\/[A-Za-z_]+)$/); // text copied from the drawn table, e.g. "23 Nov 2026, 01:37 PM Africa/Cairo"
    if (m) { var t0 = Date.parse(m[1] + (/^(UTC|GMT)$/.test(m[2]) ? ' UTC' : '')); return isNaN(t0) ? 0 : t0; }
    if (/^\d{4}-\d{2}-\d{2} /.test(s)) s = s.replace(' ', 'T');
    if (/^\d{4}-\d{2}-\d{2}T/.test(s) && !/(z|[+-]\d{2}:?\d{2})$/i.test(s)) s += 'Z';
    var t = Date.parse(s);
    return isNaN(t) ? 0 : t;
  }
  function ago(ts) {
    if (!ts) return '';
    var diff = Math.max(0, Date.now() - ts);
    var mins = Math.floor(diff / 60000);
    if (mins < 1) return '<1m';
    if (mins < 60) return mins + 'm';
    var hrs = Math.floor(mins / 60), m = mins % 60;
    if (hrs < 24) return hrs + 'h ' + m + 'm';
    return Math.floor(hrs / 24) + 'd ' + (hrs % 24) + 'h';
  }
  function parseRefs(text) {
    var seen = {}, out = [];
    String(text || '').split(/[\s,;|]+/).forEach(function (tok) {
      tok = tok.replace(/^["']+|["']+$/g, '');
      if (!tok) return;
      var ref = refLast(tok);
      if (!ref) return;
      var k = ref.toLowerCase();
      if (seen[k]) return;
      seen[k] = 1;
      out.push({ key: k, ref: ref });
    });
    return out;
  }

  /* ---------------- data store ---------------- */
  var db = { refs: {} };
  var currentList = [];
  var runNote = '';
  var activeFilter = null; // null = all rows | a state key | 'past' | 'future'
  var taValue = '';
  var batch = null;
  var running = false;
  var listAccepted = false; // set once a multi-ref query returned results: the page does accept lists
  var pendingKeys = {};
  var ppdPending = {};
  var reportRunning = false;
  var card = null, ui = null;
  var origFetch = null;
  var OPEN_KEY = 'noonCirTracker.open';
  function readOpen() { try { return localStorage.getItem(OPEN_KEY) === '1'; } catch (e) { return false; } }
  function applyOpen(o) {
    if (!card || !ui) return;
    card.classList.toggle('nct-open', o);
    ui.chev.textContent = o ? '\u25be' : '\u25b8';
    ui.head.setAttribute('aria-expanded', o ? 'true' : 'false');
  }
  function toggleOpen() {
    var o = !(card && card.classList.contains('nct-open'));
    applyOpen(o);
    try { localStorage.setItem(OPEN_KEY, o ? '1' : '0'); } catch (e) {}
  }
  var learned = {};
  function learnHeader(k, v) {
    var l = String(k).toLowerCase();
    if (l === 'n-hub' || l === 'x-locale' || l === 'x-platform') learned[l] = String(v);
  }
  function currentHub() {
    var c = document.querySelectorAll('[role="combobox"]');
    for (var i = 0; i < c.length; i++) { var t = (c[i].textContent || '').trim(); if (/^[A-Z]{2,4}-[A-Z0-9]+$/.test(t)) return t; }
    return '';
  }

  function getEntry(key, disp) {
    var e = db.refs[key];
    if (!e) e = db.refs[key] = { ref: disp || key, events: [], state: null, stateSrc: null, checkedAt: 0, snap: null };
    return e;
  }
  function evKey(ev) { return [ev.updated_at, ev.event_code, ev.username, ev.location_code, ev.location_name].join('|'); }
  function isRecord(o) {
    return o && typeof o === 'object' && !Array.isArray(o) && typeof o.job_ref === 'string' &&
      ('event_code' in o || 'updated_at' in o);
  }
  function addRecord(rec, state, src) {
    var key = refKey(rec.job_ref);
    if (!key) return;
    var e = getEntry(key, refLast(rec.job_ref));
    e.snap = null;
    var ev = {
      updated_at: str(rec.updated_at), event_code: str(rec.event_code), username: str(rec.username),
      held_reason: str(rec.held_reason), location_name: str(rec.location_name), location_code: str(rec.location_code),
      loc_type: str(rec.loc_type), loc_key: str(rec.loc_key), ts: parseTs(rec.updated_at)
    };
    var k = evKey(ev);
    var dup = false;
    for (var i = 0; i < e.events.length; i++) { if (evKey(e.events[i]) === k) { dup = true; break; } }
    if (!dup) {
      e.events.push(ev);
      e.events.sort(function (a, b) { return b.ts - a.ts; });
      if (e.events.length > MAX_EVENTS) e.events.length = MAX_EVENTS;
    }
    var ns = normState(state);
    if (ns && (src === 'net' || !e.state || e.stateSrc === 'dom')) { e.state = ns; e.stateSrc = src; }
    if (batch && batch.keys[key] && (src === 'net' || batch.mutated)) batch.seen[key] = 1;
  }
  function walk(node, st, src, depth) {
    if (!node || typeof node !== 'object' || depth > 14) return;
    if (Array.isArray(node)) { for (var i = 0; i < node.length; i++) walk(node[i], st, src, depth + 1); return; }
    if (isRecord(node)) { addRecord(node, st || node.state, src); return; }
    var ns = typeof node.state === 'string' ? node.state : st;
    for (var k in node) { var v = node[k]; if (v && typeof v === 'object') walk(v, ns, src, depth + 1); }
  }
  function ingestText(t) {
    if (typeof t !== 'string' || t.length > 30e6) return;
    t = t.trim();
    var c = t.charAt(0);
    if ((c !== '{' && c !== '[') || t.indexOf('job_ref') < 0) return;
    walk(JSON.parse(t), null, 'net', 0);
  }

  /* ---------------- DOM fallback reader ---------------- */
  function normHeader(s) { return String(s).toLowerCase().trim().replace(/[^a-z0-9]+/g, '_').replace(/^_|_$/g, ''); }
  function findHeading(t) {
    var cap = t.querySelector('caption');
    if (cap && normState(cap.textContent)) return cap.textContent;
    var el = t;
    for (var up = 0; up < 6 && el && el !== document.body; up++) {
      var s = el.previousElementSibling, hops = 0;
      while (s && hops < 6) {
        var tx = (s.textContent || '').trim();
        if (tx && tx.length < 80 && !s.querySelector('table') && normState(tx)) return tx;
        s = s.previousElementSibling; hops++;
      }
      el = el.parentElement;
    }
    return null;
  }
  function readTables() {
    var tables = document.querySelectorAll('table');
    for (var ti = 0; ti < tables.length; ti++) {
      var t = tables[ti];
      if (card && card.contains(t)) continue;
      var hc = t.querySelectorAll('thead th');
      if (!hc.length) hc = t.querySelectorAll('tr:first-child th');
      var heads = [].slice.call(hc).map(function (x) { return normHeader(x.textContent); });
      if (heads.indexOf('job_ref') < 0 || (heads.indexOf('event_code') < 0 && heads.indexOf('updated_at') < 0)) continue;
      var heading = findHeading(t);
      var rows = t.querySelectorAll('tbody tr');
      for (var ri = 0; ri < rows.length; ri++) {
        var cells = rows[ri].children, rec = {};
        for (var i = 0; i < heads.length; i++) rec[heads[i]] = cells[i] ? cells[i].textContent.trim() : '';
        if (rec.job_ref) addRecord(rec, heading, 'dom');
      }
    }
  }

  /* ---------------- network hooks ---------------- */
  function netStart() { var b = batch; if (b) { b.pending++; b.reqs++; b.lastAct = now(); } return b; }
  function netEnd(b) { if (b) { b.pending--; b.lastAct = now(); } }
  try {
    origFetch = window.fetch;
    var origSRH = XMLHttpRequest.prototype.setRequestHeader;
    XMLHttpRequest.prototype.setRequestHeader = function (k, v) {
      try { learnHeader(k, v); } catch (e) {}
      return origSRH.apply(this, arguments);
    };
    if (typeof origFetch === 'function') {
      window.fetch = function () {
        try {
          var hd = arguments[1] && arguments[1].headers;
          if (hd) { if (typeof hd.forEach === 'function' && !Array.isArray(hd)) hd.forEach(function (v, k) { learnHeader(k, v); }); else for (var hk in hd) learnHeader(hk, hd[hk]); }
        } catch (e) {}
        var b = netStart();
        var p;
        try { p = origFetch.apply(this, arguments); } catch (e) { netEnd(b); throw e; }
        p.then(function (res) {
          var c;
          try { c = res.clone(); } catch (e) { netEnd(b); return; }
          c.text().then(function (t) { try { ingestText(t); } catch (e) {} }, function () {}).then(function () { netEnd(b); });
        }, function () { netEnd(b); });
        return p;
      };
    }
    var origSend = XMLHttpRequest.prototype.send;
    XMLHttpRequest.prototype.send = function () {
      var self = this, b = netStart();
      try {
        this.addEventListener('loadend', function () {
          try {
            if (self.responseType === '' || self.responseType === 'text') ingestText(self.responseText);
            else if (self.responseType === 'json' && self.response) walk(self.response, null, 'net', 0);
          } catch (e) {}
          netEnd(b);
        });
      } catch (e) { err(e); }
      return origSend.apply(this, arguments);
    };
  } catch (e) { err('hook failed', e); }

  /* ---------------- derived view ---------------- */
  function view(key) {
    var e = db.refs[key];
    var r = { key: key, ref: '', st: 'nodata', assigned: '', loc: '', code: '', time: '', ts: 0, note: '' };
    var item = currentList.filter(function (x) { return x.key === key; })[0];
    r.ref = item ? item.ref : (e ? e.ref : key);
    r.ppd = e && e.ppd ? e.ppd : '';
    if (running && (pendingKeys[key] || ppdPending[key])) { r.st = 'pending'; return r; }
    if (e && e.snap && !e.events.length) {
      var sn = e.snap;
      r.st = sn.s; r.assigned = sn.a || ''; r.loc = sn.l || ''; r.ppd = sn.p || ''; r.ts = sn.t || 0; r.time = r.ts ? fmtLocal(r.ts) : ''; r.note = sn.n || ''; r.pickTs = sn.w || 0;
      if (r.st === 'preassigned' || r.st === 'notassigned' || r.st === 'held') r.assigned = '';
      return r;
    }
    if (!e || !e.events.length) {
      if (e && e.extra) {
        var x = e.extra;
        r.st = x.st === 'jobpending' ? 'notassigned' : x.st; r.assigned = x.assigned || ''; r.loc = x.loc || ''; r.code = x.code || ''; r.time = x.time || ''; r.ts = x.ts || 0; r.note = ((x.st === 'canceled' || x.st === 'held') && x.reason) ? x.reason : (x.note || '');
        if (r.st === 'preassigned' || r.st === 'notassigned' || r.st === 'held') r.assigned = '';
        return r;
      }
      r.note = e && e.checkedAt ? 'no events found' : 'not checked';
      return r;
    }
    var evs = e.events;
    var st = e.state;
    if (!st) {
      var code = function (x) { return x.event_code.toLowerCase(); };
      if (evs.some(function (x) { return /cancel|reject|refus/.test(code(x)); })) st = 'canceled';
      else if (evs.some(function (x) { return /picked up|picked_up|shipment received|at hub|collected/.test(code(x)); })) st = 'picked';
      else if (evs.some(function (x) { return x.username && x.username !== '-' && /task|assign/.test(code(x)); })) st = 'assigned';
      else st = 'preassigned';
    }
    // Assigned + a suspended task / held reason after the latest assignment = Attempted
    var attemptTs = 0;
    if (st === 'assigned') {
      // only actions taken after the latest task assignment (created / reassigned) count: an assignment is not an attempt
      var ti = -1;
      for (var q = 0; q < evs.length; q++) { if (/^pickup task (created|re-?assigned|assigned)/i.test(evs[q].event_code)) { ti = q; break; } }
      var after = ti >= 0 ? evs.slice(0, ti) : evs;
      // Attempted = the attempt failed or was postponed: a "Pickup task suspended" event or a held reason. "DA omw" / "DA called customer" alone are not attempts.
      var acts = after.filter(function (x) { return /suspend/i.test(x.event_code); });
      var held = after.filter(function (x) { return x.held_reason; })[0];
      if (acts.length || held) {
        st = 'attempted';
        attemptTs = Math.max(acts[0] ? acts[0].ts : 0, held ? held.ts : 0);
        // note under the state = the latest held reason only (falls back to the latest action when there is none)
        r.note = held ? held.held_reason : (acts[0] ? acts[0].event_code.replace(/\s*-\s*TK\S*$/i, '') : '');
      }
    }
    // creq-leg is the source of truth for the pickup's real state: a canceled pickup (or one that is back to pre-assigned / not assigned
    // with a job) overrides what the report events suggest. Picked always wins (the "Shipment picked up" event is definitive).
    var lg = e.leg, over = false;
    if (lg && lg.legPicked && st !== 'picked') { over = true; st = 'picked'; r.note = 'dropoff opened'; }
    else if (lg && st !== 'picked') {
      var cs = lg.st === 'jobpending' ? 'notassigned' : lg.st;
      if (cs === 'canceled' || cs === 'held' || cs === 'tpl' || ((cs === 'notassigned' || cs === 'preassigned') && lg.hasJob)) {
        over = true; st = cs; r.note = 'per creq-leg';
      }
    }
    if (st === 'canceled' || st === 'held') {
      // cancel / held reason: the current job's reason in creq-leg (the Reason column of Pickup Jobs), then the leg's held reason, then the report's latest held reason
      var rh = evs.filter(function (x) { return x.held_reason; })[0];
      r.note = (lg && lg.reason) || (rh ? rh.held_reason : '') || r.note || '';
    }
    r.st = st;
    for (var i = 0; i < evs.length; i++) { if (evs[i].username && evs[i].username !== '-') { r.assigned = evs[i].username; break; } }
    // Pre-assigned / Not assigned: the DA in the events belongs to an earlier assignment, so nothing is shown
    if (st === 'preassigned' || st === 'notassigned') r.assigned = '';
    // A new day began and the pickup has not been assigned to a DA again: Held, or Attempted on an earlier day => no DA
    if (st === 'held') r.assigned = '';
    if (st === 'attempted' && attemptTs && dayStart(attemptTs) < dayStart(Date.now())) r.assigned = '';
    // Location: "With DA" only when the pickup is really with the DA (Picked); every other state shows the hub only
    for (var j = 0; j < evs.length; j++) {
      var x = evs[j];
      if (x.location_code || x.location_name) {
        var withDa = /with\s*da/i.test(x.location_name);
        if (st === 'picked') { r.loc = withDa ? 'With DA' + (x.location_code ? ' (' + x.location_code + ')' : '') : (x.location_code || x.location_name); break; }
        r.loc = x.location_code || (withDa ? '' : x.location_name);
        if (r.loc) break;
      }
    }
    if (!r.loc && lg && lg.hub) r.loc = lg.hub;
    if (st === 'picked' && /^With DA/.test(r.loc)) {
      var pe = evs.filter(function (x) { return /picked up|picked_up|collected/i.test(x.event_code) && !/at hub|received/i.test(x.event_code); })[0];
      r.pickTs = pe ? pe.ts : evs[0].ts;
    }
    r.code = evs[0].event_code; r.ts = evs[0].ts; r.time = evs[0].ts ? fmtLocal(evs[0].ts) : evs[0].updated_at;
    // Last event of a shipment with report events is always the report's last event (creq-leg timestamps only fill in when there are none)
    return r;
  }
  function allRows() {
    var rows = currentList.map(function (it, i) { var v = view(it.key); v.i = i; return v; });
    var order = {}; STATES.concat(['pending']).forEach(function (s, i) { order[s] = s === 'pending' ? 1.5 : i; });
    rows.sort(function (a, b) { return (order[a.st] - order[b.st]) || (a.i - b.i); });
    return rows;
  }

  /* ---------------- persistence ---------------- */
  var saveTimer = null;
  var snapCache = [];
  function takeSnap() {
    // compact copy of the derived rows (~150 chars per ref) - this is what gets saved, so thousands of refs fit in the browser storage
    try {
      snapCache = allRows().filter(function (r) { return r.st !== 'pending'; }).map(function (r) {
        return { k: r.key, r: r.ref, s: r.st, a: r.assigned, l: r.loc, p: r.ppd, t: r.ts, n: r.note, w: r.pickTs || 0 };
      });
    } catch (e) { err('snap', e); }
  }
  function persist() {
    clearTimeout(saveTimer);
    saveTimer = setTimeout(function () {
      try { localStorage.setItem(LS_KEY, JSON.stringify({ v: 2, text: taValue, snap: snapCache, savedAt: Date.now() })); }
      catch (e) {
        err('save failed', e);
        if (ui && ui.prog && !/storage is full/.test(ui.prog.textContent)) ui.prog.textContent += ' (results could not be saved: browser storage is full)';
      }
    }, 250);
  }
  function restore() {
    try {
      var raw = localStorage.getItem(LS_KEY);
      if (!raw) return;
      var o = JSON.parse(raw);
      if (o && o.v === 2) {
        taValue = o.text || '';
        currentList = parseRefs(taValue);
        snapCache = o.snap || [];
        snapCache.forEach(function (x) { var en = getEntry(x.k, x.r); en.snap = x; en.ppd = x.p || ''; en.checkedAt = 1; });
      } else if (o && o.v === 1) { // saves made by older versions
        taValue = o.text || '';
        if (o.db && o.db.refs) db = o.db;
        currentList = parseRefs(taValue);
        Object.keys(db.refs).forEach(function (k) {
          var en = db.refs[k];
          (en.events || []).forEach(function (ev) { ev.ts = parseTs(ev.updated_at); });
          if (en.events) en.events.sort(function (a, b) { return b.ts - a.ts; });
        });
        takeSnap();
      }
    } catch (e) { err('restore failed', e); }
  }

  /* ---------------- UI ---------------- */
  function h(tag, props) {
    var el = document.createElement(tag);
    if (props) for (var k in props) {
      var v = props[k];
      if (k === 'class') el.className = v;
      else if (k === 'style') el.style.cssText = v;
      else if (k.slice(0, 2) === 'on') el.addEventListener(k.slice(2), v);
      else if (v !== false && v != null) el.setAttribute(k, v);
    }
    for (var i = 2; i < arguments.length; i++) {
      var c = arguments[i];
      if (c == null || c === false) continue;
      el.appendChild(c.nodeType ? c : document.createTextNode(String(c)));
    }
    return el;
  }
  var CSS = [
    '#nct-card{background:#fff;border:1px solid #e2e5f1;border-radius:10px;padding:12px 14px;margin:12px 0;font-family:"Segoe UI",Arial,sans-serif;font-size:13px;color:#404553;box-sizing:border-box;max-width:100%}',
    '#nct-card *{box-sizing:border-box}',
    '#nct-card .nct-head{display:flex;align-items:center;gap:8px;cursor:pointer;user-select:none;outline:none}',
    '#nct-card.nct-open .nct-head{margin-bottom:8px}',
    '#nct-card .nct-title{font-weight:600;font-size:14px}',
    '#nct-card .nct-chev{display:inline-block;width:14px;color:#7e859b;font-size:12px}',
    '#nct-card .nct-sum{margin-left:auto;font-size:12px;color:#7e859b}',
    '#nct-card:not(.nct-open) .nct-body{display:none}',
    '#nct-card:not(.nct-open){padding-top:9px;padding-bottom:9px}',
    '#nct-card textarea{width:100%;min-height:84px;max-height:240px;resize:vertical;border:1px solid #e2e5f1;border-radius:6px;padding:8px 10px;font:12.5px/1.4 Consolas,"Segoe UI",monospace;color:#404553}',
    '#nct-card .nct-btns{display:flex;flex-wrap:wrap;gap:8px;margin:8px 0}',
    '#nct-card button.nct-b{border:1px solid #cfd4e6;background:#fff;color:#404553;border-radius:6px;padding:6px 12px;font:600 12.5px "Segoe UI",Arial,sans-serif;cursor:pointer}',
    '#nct-card button.nct-b:hover{background:#f3f5fb}',
    '#nct-card button.nct-b:disabled{opacity:.5;cursor:default}',
    '#nct-card button.nct-p{background:#3866df;border-color:#3866df;color:#fff}',
    '#nct-card button.nct-p:hover{background:#2f57c0}',
    '#nct-card .nct-prog{min-height:18px;color:#5b6477;font-size:12.5px;margin:2px 0 8px}',
    '#nct-card .nct-counts{display:flex;flex-wrap:wrap;gap:6px;margin-bottom:8px}',
    '#nct-card .nct-cnt{border-radius:12px;padding:3px 10px;font-size:12px;font-weight:600;color:#2b3440}',
    '#nct-card .nct-cnt.z{opacity:.45}',
    '#nct-card .nct-cnt.nct-click{cursor:pointer;user-select:none;outline:none}',
    '#nct-card .nct-cnt.nct-click:hover{filter:brightness(.95)}',
    '#nct-card .nct-cnt.z.nct-click{cursor:default}',
    '#nct-card .nct-cnt.act{box-shadow:0 0 0 2px #3866df;opacity:1}',
    '#nct-card .nct-empty td{text-align:center;color:#7e859b;padding:14px}',
    '#nct-card .nct-wrap{overflow-x:auto}',
    '#nct-card table.nct-t{width:100%;border-collapse:collapse}',
    '#nct-card .nct-t th{text-align:left;font-size:11.5px;color:#7e859b;font-weight:600;padding:6px 8px;border-bottom:1px solid #e2e5f1;white-space:nowrap}',
    '#nct-card .nct-t td{padding:6px 8px;border-bottom:1px solid rgba(0,0,0,.06);vertical-align:top;color:#2b3440}',
    '#nct-card .nct-ref{cursor:pointer;font-family:Consolas,monospace;font-weight:600;white-space:nowrap}',
    '#nct-card .nct-ref:hover{text-decoration:underline}',
    '#nct-card .nct-ago{display:inline-block;margin-left:8px;padding:1px 9px;border-radius:999px;background:rgba(255,255,255,.85);color:#17406b;font-size:11px;font-weight:700;white-space:nowrap;vertical-align:1px;box-shadow:0 0 0 1px rgba(0,0,0,.07)}',
    '#nct-card .nct-ago::before{content:"";display:inline-block;width:5px;height:5px;border-radius:50%;background:#3b82c4;margin-right:5px;vertical-align:1px}',
    '#nct-card .nct-late{display:inline-block;margin-left:8px;padding:1px 8px;border-radius:999px;background:#ffd0cb;color:#a4160c;font-size:11px;font-weight:700;vertical-align:1px}',
    '#nct-card .nct-flag{display:inline-block;margin-left:8px;padding:1px 8px;border-radius:999px;background:#d93025;color:#fff;font-size:11px;font-weight:700;vertical-align:1px}',
    '#nct-card .nct-soon{display:inline-block;margin-left:8px;padding:1px 8px;border-radius:999px;background:#d6e8ff;color:#0b4f7a;font-size:11px;font-weight:700;vertical-align:1px}',
    '#nct-card .nct-sub{font-size:11px;color:#5b6477}',
    '#nct-card .nct-re{border:0;background:transparent;cursor:pointer;font-size:15px;color:#3866df;padding:0 4px}',
    '#nct-card .nct-re:disabled{opacity:.4;cursor:default}',
    '@media (max-width:640px){#nct-card{padding:10px}#nct-card .nct-c-last{display:none}#nct-card .nct-t td,#nct-card .nct-t th{padding:5px 5px;font-size:12px}}'
  ].join('\n');

  function copyText(text) {
    function fallback() {
      var ta = h('textarea', { style: 'position:fixed;left:-9999px;top:0' });
      ta.value = text; document.body.appendChild(ta); ta.select();
      try { document.execCommand('copy'); } catch (e) {}
      ta.remove();
    }
    try {
      if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(text).catch(fallback);
      else fallback();
    } catch (e) { fallback(); }
  }
  function setProg(t) { if (ui) ui.prog.textContent = t; }

  var LATE_STATES = { assigned: 1, attempted: 1, preassigned: 1, notassigned: 1 };
  function ppdDelta(r) {
    // whole days between today and the PPD (positive = PPD passed, negative = PPD still ahead); only for shipments not picked yet
    if (!r.ppd || !LATE_STATES[r.st]) return null;
    var m = /^(\d{4})-(\d{2})-(\d{2})/.exec(r.ppd);
    if (!m) return null;
    var d0 = new Date(+m[1], +m[2] - 1, +m[3]).getTime(), t = new Date(); t = new Date(t.getFullYear(), t.getMonth(), t.getDate()).getTime();
    return Math.round((t - d0) / 86400000);
  }
  function withDaDays(r) {
    // Picked on an earlier calendar day and still with the DA (latest location is "With DA") -> number of days, else 0
    if (r.st !== 'picked' || !r.pickTs || !/^With DA/.test(r.loc || '')) return 0;
    var d = new Date(r.pickTs), d0 = new Date(d.getFullYear(), d.getMonth(), d.getDate()).getTime();
    var t = new Date(); t = new Date(t.getFullYear(), t.getMonth(), t.getDate()).getTime();
    var n = Math.round((t - d0) / 86400000);
    return n > 0 ? n : 0;
  }
  function dayStart(ts) { var d = new Date(ts); return new Date(d.getFullYear(), d.getMonth(), d.getDate()).getTime(); }
  function lateDays(r) { var n = ppdDelta(r); return n !== null && n > 0 ? n : 0; }
  function futureDays(r) { var n = ppdDelta(r); return n !== null && n < 0 ? -n : 0; }
  function rowVisible(r) {
    if (!activeFilter) return true;
    if (activeFilter === 'past') return lateDays(r) > 0;
    if (activeFilter === 'future') return futureDays(r) > 0;
    if (activeFilter === 'withda') return withDaDays(r) > 0;
    return r.st === activeFilter;
  }
  function filterName() {
    if (!activeFilter) return '';
    return activeFilter === 'past' ? 'Past PPD' : activeFilter === 'future' ? 'Future PPD' : activeFilter === 'withda' ? 'With DA 1d+' : (LABEL[activeFilter] || activeFilter);
  }
  function setFilter(key) { activeFilter = (key === activeFilter) ? null : key; render(); }
  function chip(label, key, n, style, title) {
    var on = key !== null && activeFilter === key;
    return h('span', {
      class: 'nct-cnt nct-click' + (n || key === null ? '' : ' z') + (on ? ' act' : ''), style: style, title: title || (key === null ? 'Show all' : 'Click to filter / click again to clear'),
      role: 'button', tabindex: '0', 'aria-pressed': on ? 'true' : 'false',
      onclick: function () { if (n || on || key === null) setFilter(key); },
      onkeydown: function (ev) { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); if (n || on || key === null) setFilter(key); } }
    }, label + ' ' + n);
  }
  var renderQueued = false;
  function scheduleRender() {
    if (renderQueued) return;
    renderQueued = true;
    setTimeout(function () { renderQueued = false; render(); }, currentList.length > 300 ? 700 : 60);
  }
  function render() {
    if (!ui) return;
    try {
      var rows = allRows();
      var counts = {};
      STATES.forEach(function (s) { counts[s] = 0; });
      rows.forEach(function (r) { if (counts[r.st] != null) counts[r.st]++; });
      var shown = rows.filter(rowVisible);
      ui.sum.textContent = rows.length ? (activeFilter ? shown.length + ' of ' + rows.length + ' refs \u00b7 ' + filterName() : rows.length + ' refs') + (running ? ' \u00b7 running...' : '') : '';
      ui.counts.textContent = '';
      ui.counts.appendChild(chip('Total', null, rows.length, 'background:#eef0f7', 'Show all'));
      STATES.forEach(function (s) {
        if (s === 'nodata' || (s === 'tpl' && !counts.tpl)) return;
        ui.counts.appendChild(chip(LABEL[s], s, counts[s], 'background:' + COLOR[s]));
      });
      var pastN = rows.filter(function (r) { return lateDays(r) > 0; }).length;
      ui.counts.appendChild(chip('Past PPD', 'past', pastN, 'background:#ffd0cb;color:#a4160c', 'Past PPD and not picked yet - click to filter'));
      var futN = rows.filter(function (r) { return futureDays(r) > 0; }).length;
      ui.counts.appendChild(chip('Future PPD', 'future', futN, 'background:#d6e8ff;color:#0b4f7a', 'PPD still ahead and not picked yet - click to filter'));
      var daN = rows.filter(function (r) { return withDaDays(r) > 0; }).length;
      ui.counts.appendChild(chip('With DA 1d+', 'withda', daN, 'background:#d93025;color:#fff', 'Picked on an earlier day and still with the DA - click to filter'));
      ui.tbody.textContent = '';
      if (!shown.length && rows.length) ui.tbody.appendChild(h('tr', { class: 'nct-empty' }, h('td', { colspan: '7' }, 'No rows match this filter')));
      var frag = document.createDocumentFragment();
      shown.forEach(function (r) {
        var bg = COLOR[r.st] || '#fff';
        var tr = h('tr', { style: 'background:' + bg });
        tr.appendChild(h('td', { class: 'nct-ref', title: 'Click to copy', onclick: function () { copyText(r.ref); setProg('Copied ' + r.ref); } }, r.ref));
        tr.appendChild(h('td', { style: 'font-weight:600;white-space:nowrap' }, LABEL[r.st] || r.st, 
          withDaDays(r) ? h('span', { class: 'nct-flag', title: 'Picked on ' + fmtLocal(r.pickTs).slice(0, 10) + ' and still with the DA' }, 'With DA ' + withDaDays(r) + 'd') : null,
          r.note ? h('div', { class: 'nct-sub' }, r.note) : null));
        tr.appendChild(h('td', null, r.assigned || '-'));
        tr.appendChild(h('td', null, r.loc || '-'));
        var late = lateDays(r);
        tr.appendChild(h('td', { style: 'white-space:nowrap' }, ppdPending[r.key] ? '...' : (r.ppd || '-'),
          late ? h('span', { class: 'nct-late', title: 'Past PPD and not picked yet' }, late + 'd late') : null,
          futureDays(r) ? h('span', { class: 'nct-soon', title: 'PPD still ahead' }, 'in ' + futureDays(r) + 'd') : null));
        tr.appendChild(h('td', { class: 'nct-c-last' }, r.time ? h('div', null, r.time, r.ts ? h('span', { class: 'nct-ago', title: 'Time since this action' }, ago(r.ts) + ' ago') : null) : '-'));
        tr.appendChild(h('td', null, h('button', { class: 'nct-re', title: 'Re-check', disabled: running ? 'disabled' : false, onclick: function () { if (!running) runRefs([r.key], false); } }, '\u21bb')));
        frag.appendChild(tr);
      });
      ui.tbody.appendChild(frag);
      ui.btnTrack.disabled = running; ui.btnClear.disabled = running;
    } catch (e) { err('render', e); }
  }
  function toTSV() {
    var lines = [['Job ref', 'State', 'Assigned to', 'Location', 'PPD', 'Days past PPD', 'Days to PPD', 'Days with DA', 'Last event', 'Last event time', 'Ago', 'Note'].join('\t')];
    allRows().filter(rowVisible).forEach(function (r) {
      lines.push([r.ref, LABEL[r.st] || r.st, r.assigned, r.loc, r.ppd, lateDays(r) || '', futureDays(r) || '', withDaDays(r) || '', r.code, r.time, ago(r.ts), r.note].map(function (x) { return String(x || '').replace(/[\t\r\n]+/g, ' '); }).join('\t'));
    });
    return lines.join('\n');
  }

  function build() {
    var ta = h('textarea', { placeholder: 'Paste CIRs here: one per line or separated by comma / space / ; / |  (noon::RPK-... is fine)', spellcheck: 'false' });
    ta.value = taValue;
    ta.addEventListener('input', function () { taValue = ta.value; persist(); });
    var btnTrack = h('button', { class: 'nct-b nct-p', type: 'button', onclick: trackAll }, 'Track all');
    var btnCopy = h('button', { class: 'nct-b', type: 'button', onclick: function () { copyText(toTSV()); setProg('Table copied (TSV)' + (activeFilter ? ' - filtered: ' + filterName() : '')); } }, 'Copy table');
    var btnClear = h('button', { class: 'nct-b', type: 'button', onclick: clearAll }, 'Clear');
    var prog = h('div', { class: 'nct-prog' });
    var counts = h('div', { class: 'nct-counts' });
    var tbody = h('tbody');
    var table = h('table', { class: 'nct-t' },
      h('thead', null, h('tr', null, h('th', null, 'Job ref'), h('th', null, 'State'), h('th', null, 'Assigned to'), h('th', null, 'Location'), h('th', null, 'PPD'), h('th', { class: 'nct-c-last' }, 'Last event'), h('th', null, ''))),
      tbody);
    var chev = h('span', { class: 'nct-chev' }, '\u25b8');
    var sum = h('span', { class: 'nct-sum' });
    var head = h('div', { class: 'nct-head', role: 'button', tabindex: '0', title: 'Show / hide the tracker', onclick: toggleOpen,
      onkeydown: function (ev) { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); toggleOpen(); } } },
      chev, h('span', { class: 'nct-title' }, 'CIR bulk tracker'), sum);
    var body = h('div', { class: 'nct-body' }, ta,
      h('div', { class: 'nct-btns' }, btnTrack, btnCopy, btnClear), prog, counts, h('div', { class: 'nct-wrap' }, table));
    var el = h('div', { id: CARD_ID }, head, body);
    ui = { head: head, chev: chev, sum: sum, ta: ta, btnTrack: btnTrack, btnCopy: btnCopy, btnClear: btnClear, prog: prog, counts: counts, tbody: tbody };
    return el;
  }

  /* ---------------- querying ---------------- */
  function findForm() {
    var i = document.querySelector('input[name="job_refs"]');
    return i ? (i.form || i.closest('form')) : null;
  }
  function setInput(input, v) {
    var setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
    setter.call(input, v);
    input.dispatchEvent(new Event('input', { bubbles: true }));
    input.dispatchEvent(new Event('change', { bubbles: true }));
  }
  function submitForm(form) {
    var btn = form.querySelector('button[type="submit"]');
    if (btn && !btn.disabled) btn.click();
    else if (typeof form.requestSubmit === 'function') form.requestSubmit();
    else form.dispatchEvent(new Event('submit', { bubbles: true, cancelable: true }));
  }
  function settle(b) {
    return new Promise(function (resolve) {
      var iv = setInterval(function () {
        var t = now(), quiet = t - b.lastAct;
        var how = null;
        if (b.reqs > 0 && b.pending <= 0 && quiet >= QUIET_MS) how = 'settled';
        else if (b.reqs === 0 && b.mutated && quiet >= 1000) how = 'settled-dom';
        else if (b.reqs === 0 && !b.mutated && t - b.t0 > NO_ACTIVITY_MS) how = 'no-activity';
        else if (t - b.t0 >= b.max) how = 'timeout';
        if (how) { clearInterval(iv); resolve(how); }
      }, 40);
    });
  }
  function displayOf(key) {
    var it = currentList.filter(function (x) { return x.key === key; })[0];
    return it ? it.ref : (db.refs[key] ? db.refs[key].ref : key);
  }
  async function queryBatch(keys, max) {
    var form = findForm();
    if (!form) throw new Error('job_refs form not found');
    var input = form.querySelector('input[name="job_refs"]');
    var keyMap = {}; keys.forEach(function (k) { keyMap[k] = 1; });
    batch = { keys: keyMap, seen: {}, pending: 0, reqs: 0, mutated: false, t0: now(), lastAct: now(), max: max };
    setInput(input, keys.map(displayOf).join(','));
    await sleep(0);
    batch.t0 = now(); batch.lastAct = now(); batch.mutated = false;
    submitForm(form);
    var how = await settle(batch);
    if (!Object.keys(batch.seen).some(function (k) { return batch.seen[k]; })) { try { readTables(); } catch (e) { err('readTables', e); } } // DOM fallback only when no network data arrived
    var b = batch; batch = null;
    return { seen: b.seen, nSeen: Object.keys(b.seen).length, how: how, reqs: b.reqs };
  }
  function chunk(arr, n) { var o = []; for (var i = 0; i < arr.length; i += n) o.push(arr.slice(i, i + n)); return o; }

  /* ---------- creq-leg lookup for refs the report has no events for ---------- */
  function pad2(n) { return (n < 10 ? '0' : '') + n; }
  function fmtLocal(ts) {
    var d = new Date(ts), hr = d.getHours();
    return d.getFullYear() + '-' + pad2(d.getMonth() + 1) + '-' + pad2(d.getDate()) + ' ' + pad2(hr % 12 || 12) + ':' + pad2(d.getMinutes()) + ' ' + (hr >= 12 ? 'PM' : 'AM');
  }
  function parseUtc(v) {
    if (!v) return 0;
    var s = String(v).trim();
    if (!/(z|[+-]\d{2}:?\d{2})$/i.test(s)) s += 'Z';
    var t = Date.parse(s);
    return isNaN(t) ? 0 : t;
  }
  async function fetchLeg(ref) {
    if (typeof origFetch !== 'function') return { error: 'fetch unavailable' };
    var hd = { 'content-type': 'application/json', 'accept': 'application/json, text/plain, */*',
      'x-platform': learned['x-platform'] || 'web', 'x-locale': learned['x-locale'] || 'uae-en' };
    var hub = learned['n-hub'] || currentHub();
    if (hub) hd['n-hub'] = hub;
    var ctl = typeof AbortController === 'function' ? new AbortController() : null;
    var to = setTimeout(function () { if (ctl) ctl.abort(); }, SINGLE_MAX_MS);
    try {
      var res = await origFetch.call(window, LEG_URL, { method: 'POST', headers: hd, body: JSON.stringify({ client_ref: ref }), credentials: 'same-origin', priority: 'high', signal: ctl ? ctl.signal : undefined });
      if (res.status === 429) return { rate: true };
      if (!res.ok) return { error: 'HTTP ' + res.status };
      return { json: await res.json() };
    } catch (e) { return { error: e && e.name === 'AbortError' ? 'timeout' : String(e && e.message || e) }; }
    finally { clearTimeout(to); }
  }
  function mapJobStatus(v) {
    var x = String(v || '').toLowerCase().replace(/[^a-z0-9]+/g, '_');
    if (!x) return null;
    if (/cancel/.test(x)) return 'canceled';
    if (/pre_?assigned/.test(x)) return 'preassigned';
    if (/not_?assigned|unassigned|pending/.test(x)) return 'notassigned'; // Pending == Not assigned
    if (/assigned|locked/.test(x)) return 'assigned'; // locked = job is held by a DA
    if (/picked|complet|success|done/.test(x)) return 'picked';
    return null;
  }
  function hasTplSignal(node, depth) {
    depth = depth || 0;
    if (node == null || depth > 12) return false;
    if (typeof node === 'string') return /^\s*tpl\s*$/i.test(node) || /platform_system/i.test(node);
    if (typeof node !== 'object') return false;
    if (Array.isArray(node)) return node.some(function (x) { return hasTplSignal(x, depth + 1); });
    if (node.is_tpl_dashboard === 1 || node.is_tpl_dashboard === true) return true;
    for (var k in node) { if (hasTplSignal(node[k], depth + 1)) return true; }
    return false;
  }
  function legToExtra(j) {
    var rows = (j && j.rows) || [];
    if (!rows.length) return { st: 'nodata', ppd: '', note: 'not found in creq-leg', checkedAt: Date.now() };
    rows = rows.slice().sort(function (a, b) {
      var al = a.creq_leg || {}, bl = b.creq_leg || {};
      var ap = al.creq_leg_type === 'pickup' ? 1 : 0, bp = bl.creq_leg_type === 'pickup' ? 1 : 0;
      return (bp - ap) || (parseUtc(bl.created_at) - parseUtc(al.created_at));
    });
    var r = rows[0], leg = r.creq_leg || {}, creq = r.creq || {};
    var jobs = (r.creq_leg_jobs || []).slice().sort(function (a, b) { // current job = the active one, else the newest attempt (an old attempt can be updated later, e.g. when it gets canceled)
      return ((b.is_active ? 1 : 0) - (a.is_active ? 1 : 0)) || ((b.id_creq_leg_job || 0) - (a.id_creq_leg_job || 0)) || (parseUtc(b.created_at) - parseUtc(a.created_at));
    });
    var job = jobs[0] || null;
    var ppd = str(leg.scheduled_date);
    var jobSt = job ? str(job.job_status) : '', legSt = str(leg.creq_leg_status), creqSt = str(creq.creq_status);
    var assigned = job ? str(job.assigned_username || job.assigned_user) : '';
    // last update = newest updated_at across every job and leg in the response
    var lastTs = 0;
    rows.forEach(function (x) {
      lastTs = Math.max(lastTs, parseUtc((x.creq_leg || {}).updated_at));
      (x.creq_leg_jobs || []).forEach(function (jb) { lastTs = Math.max(lastTs, parseUtc(jb.updated_at)); });
    });
    // state = the latest job's Job Status only (falls back to the leg status when there is no job)
    var st = mapJobStatus(job ? jobSt : legSt);
    var unknown = st ? '' : (job ? jobSt : legSt);
    if (!st) st = 'nodata';
    // a dropoff leg that is opened = the shipment was picked up and moved on to its dropoff (a canceled pickup + TPL item without it is just Canceled)
    var dropLeg = null;
    rows.forEach(function (x) {
      var l = x.creq_leg || {};
      if (x !== r && /drop/i.test(l.creq_leg_type || '') && /open/i.test(l.creq_leg_status || '') && !dropLeg) dropLeg = l;
    });
    if (dropLeg) {
      return {
        st: 'picked', legPicked: true, hasJob: !!job, ppd: ppd, assigned: assigned, loc: str(dropLeg.hub_code || dropLeg.hub_sector_code || leg.hub_code), hub: str(dropLeg.hub_code),
        code: 'Pickup ' + legSt + ', dropoff ' + str(dropLeg.creq_leg_status), time: lastTs ? fmtLocal(lastTs) : '', ts: lastTs,
        note: 'dropoff opened', checkedAt: Date.now()
      };
    }
    var reason = job ? str(job.reason_code || job.cleg_held_reason) : '';
    if (!reason) reason = str(leg.held_reason_code);
    if (/held/i.test(legSt) && (st === 'canceled' || st === 'nodata')) { st = 'held'; unknown = ''; reason = str(leg.held_reason_code) || reason; } // pickup leg is held (not canceled)
    var ts = lastTs || parseUtc((job && job.updated_at) || leg.updated_at);
    var note = [unknown ? 'unknown status: ' + unknown : '', 'leg ' + legSt, job ? 'job ' + jobSt + (jobs.length > 1 ? ' (latest of ' + jobs.length + ')' : '') : 'no job', reason ? 'reason ' + reason : '', creqSt ? 'creq ' + creqSt : ''].filter(Boolean).join(' \u00b7 ');
    return {
      st: st, reason: reason, hasJob: !!job, ppd: ppd, assigned: assigned, loc: str(leg.hub_code || leg.hub_sector_code), hub: str(leg.hub_code),
      code: job ? 'Job: ' + jobSt : 'Leg: ' + legSt, time: ts ? fmtLocal(ts) : '', ts: ts,
      note: 'creq-leg: ' + note, checkedAt: Date.now()
    };
  }
  async function lookupLegs(keys) {
    // runs in parallel with the report query; stores PPD + the creq-leg state for every ref.
    // Adaptive concurrency: starts wide, halves and backs off on 429 (the ref is retried), creeps back up on success.
    var list = keys.slice(0, LOOKUP_MAX);
    var out = { n: 0, errs: 0, rate: false, total: list.length };
    if (!list.length) return out;
    list.forEach(function (k) { ppdPending[k] = 1; });
    var q = list.slice(), inflight = 0, limit = LEG_START, okStreak = 0, backoffUntil = 0, hits = 0, stop = false, retrying = 0, attempts = {};
    await new Promise(function (resolve) {
      function pump() {
        if (stop || !q.length) { if (inflight === 0 && retrying === 0) resolve(); return; }
        var wait = backoffUntil - now();
        if (wait > 0) { setTimeout(pump, wait + 5); return; }
        while (inflight < limit && q.length) launch(q.shift());
      }
      async function launch(k) {
        inflight++;
        var r = await fetchLeg(displayOf(k));
        inflight--;
        if (r.rate) {
          q.unshift(k); // the ref is retried, never dropped
          if (now() >= backoffUntil) { // one backoff per wave of 429s, exponential, give up only after 6 waves in a row
            hits++; okStreak = 0; limit = Math.max(LEG_MIN, Math.floor(limit / 2));
            backoffUntil = now() + Math.min(1200 * Math.pow(2, hits - 1), 8000);
            if (hits >= 6) { stop = true; out.rate = true; }
          }
          pump(); return;
        }
        hits = 0;
        if (!r.json && !/^HTTP 4/.test(r.error || '') && (attempts[k] = (attempts[k] || 0) + 1) < 3) {
          // transient failure (network error, timeout, 5xx): retry the ref instead of losing it
          retrying++; await sleep(200 * attempts[k]); retrying--;
          q.push(k); pump(); return;
        }
        var en = getEntry(k, displayOf(k));
        if (r.json) {
          try { var x = legToExtra(r.json); en.ppd = x.ppd || ''; en.ppdAt = Date.now(); en.leg = x; en.extra = x; en.snap = null; }
          catch (e) { out.errs++; err(e); en.extra = { st: 'nodata', note: 'creq-leg parse error', checkedAt: Date.now() }; }
        } else {
          out.errs++;
          en.extra = { st: 'nodata', note: 'creq-leg lookup failed: ' + r.error, checkedAt: Date.now() };
        }
        out.n++;
        delete ppdPending[k];
        okStreak++; if (okStreak >= 8 && limit < LEG_MAX) { limit++; okStreak = 0; }
        if (!reportRunning) setProg('creq-leg lookup ' + out.n + '/' + list.length + ': ' + displayOf(k));
        scheduleRender();
        pump();
      }
      pump();
    });
    list.forEach(function (k) {
      if (ppdPending[k]) {
        var en2 = getEntry(k, displayOf(k));
        if (!en2.extra) en2.extra = { st: 'nodata', note: 'creq-leg lookup skipped (rate limited, try again)', checkedAt: Date.now() };
        delete ppdPending[k];
      }
    });
    return out;
  }

  async function runRefs(keys, allowFallback) {
    if (running) return;
    running = true;
    var t0 = now(), queries = 0, fb = 0, notes = [];
    pendingKeys = {}; keys.forEach(function (k) { pendingKeys[k] = 1; });
    render();
    var legP = lookupLegs(keys).catch(function (e) { err('lookup', e); return { n: 0, errs: 1, rate: false }; });
    reportRunning = true;
    try {
      var chunks = chunk(keys, BATCH_SIZE);
      for (var ci = 0; ci < chunks.length; ci++) {
        var ck = chunks[ci];
        var eta = '';
        if (ci > 0) { var left = Math.round(((now() - t0) / ci) * (chunks.length - ci) / 1000); eta = ' \u00b7 ~' + (left >= 90 ? Math.round(left / 60) + 'm' : left + 's') + ' left'; }
        setProg('Batch ' + (ci + 1) + '/' + chunks.length + ': querying ' + ck.length + ' refs in one request...' + eta);
        var r = await queryBatch(ck, BATCH_MAX_MS);
        queries++;
        if (r.nSeen === 0 && (r.how === 'timeout' || r.how === 'no-activity')) { // no answer at all: ask once more before giving up on this batch
          setProg('Batch ' + (ci + 1) + '/' + chunks.length + ': no response, retrying once...');
          r = await queryBatch(ck, BATCH_MAX_MS);
          queries++;
          notes.push('batch ' + (ci + 1) + ' retried');
        }
        if (r.how === 'timeout') notes.push('batch ' + (ci + 1) + ' timed out');
        var skipped = {};
        if (r.nSeen > 0 && ck.length > 1) listAccepted = true;
        if (r.nSeen === 0 && ck.length > 1 && allowFallback && !listAccepted) {
          notes.push('list not accepted, fallback');
          for (var i = 0; i < ck.length; i++) {
            if (fb >= FALLBACK_MAX) { skipped[ck[i]] = 1; continue; }
            fb++;
            setProg('Fallback ' + fb + '/' + Math.min(ck.length, FALLBACK_MAX) + ': ' + displayOf(ck[i]));
            await queryBatch([ck[i]], SINGLE_MAX_MS);
            queries++;
            var en = db.refs[ck[i]]; if (en) en.checkedAt = Date.now(); else getEntry(ck[i], displayOf(ck[i])).checkedAt = Date.now();
            delete pendingKeys[ck[i]];
            render();
          }
          if (Object.keys(skipped).length) notes.push(Object.keys(skipped).length + ' refs not checked (fallback limit ' + FALLBACK_MAX + ')');
        }
        ck.forEach(function (k) {
          if (skipped[k]) return;
          getEntry(k, displayOf(k)).checkedAt = Date.now();
          delete pendingKeys[k];
        });
        if (chunks.length > 4) scheduleRender(); else render();
        if ((ci + 1) % 10 === 0) { takeSnap(); persist(); } // keep partial progress safe on long runs
        if (ci < chunks.length - 1) await sleep(GAP_MS);
      }
      reportRunning = false;
      var lk = await legP;
      if (runNote) { notes.push(runNote); runNote = ''; }
      if (lk.n) notes.push(lk.n + ' creq-leg lookups');
      if (lk.errs) notes.push(lk.errs + ' lookup errors');
      if (lk.rate) notes.push('rate limited (429)');
      setProg('Done: ' + keys.length + ' refs in ' + ((now() - t0) / 1000).toFixed(1) + 's, ' + queries + ' report quer' + (queries === 1 ? 'y' : 'ies') + (notes.length ? ' (' + notes.join('; ') + ')' : ''));
    } catch (e) {
      err('run failed', e);
      setProg('Error: ' + (e && e.message ? e.message : e));
    } finally {
      running = false; reportRunning = false; pendingKeys = {}; ppdPending = {}; batch = null;
      render(); takeSnap(); persist();
    }
  }
  function trackAll() {
    try {
      if (running) return;
      taValue = ui.ta.value;
      var list = parseRefs(taValue);
      if (!list.length) { setProg('Paste at least one CIR first'); return; }
      if (list.length > MAX_REFS) { runNote = (list.length - MAX_REFS) + ' refs beyond the ' + MAX_REFS + ' limit were not processed - paste them in a second run'; list = list.slice(0, MAX_REFS); }
      currentList = list; activeFilter = null;
      persist();
      runRefs(list.map(function (x) { return x.key; }), true);
    } catch (e) { err(e); }
  }
  function clearAll() {
    if (running) return;
    db = { refs: {} }; currentList = []; taValue = ''; activeFilter = null; snapCache = [];
    if (ui) ui.ta.value = '';
    try { localStorage.removeItem(LS_KEY); } catch (e) {}
    setProg('Cleared'); render();
  }

  /* ---------------- mount / SPA handling ---------------- */
  function urlMatch() {
    var p = location.pathname.replace(/\/+$/, '').split('/');
    return p[p.length - 1] === PAGE_CODE && p.indexOf('reports') >= 0;
  }
  function titleMatch() {
    // the report name shown in the page header (cir_pickup_tracker) - works even when the URL is stale / changes late
    var hs = document.querySelectorAll('h1,h2,h3,h4,h5,h6');
    for (var i = 0; i < hs.length; i++) { if (hs[i].textContent.trim().toLowerCase() === PAGE_CODE) return true; }
    return false;
  }
  function placeholderMatch() {
    // unique to this report's form: "Job refs, comma separated (client_code::client_ref or client_ref)?"
    var i = document.querySelector('input[name="job_refs"]');
    return !!i && /client_code::client_ref/i.test(i.getAttribute('placeholder') || '');
  }
  // The address bar can be stale (SPA navigation), so the page is recognised by its own content as well as by the URL
  function onCirPage() { return titleMatch() || placeholderMatch() || urlMatch(); }
  function removeCard() {
    var olds = document.querySelectorAll('#' + CARD_ID);
    for (var i = 0; i < olds.length; i++) olds[i].remove();
    card = null; ui = null;
  }
  function mount(form) {
    removeCard();
    if (!document.getElementById(STYLE_ID)) {
      var st = h('style', { id: STYLE_ID }); st.textContent = CSS; document.head.appendChild(st);
    }
    var anchor = form.closest('.MuiPaper-root') || form;
    if (!anchor.parentElement) return;
    card = build();
    anchor.parentElement.insertBefore(card, anchor);
    applyOpen(readOpen());
    render();
  }
  function ensure() {
    try {
      if (!onCirPage()) { if (card) removeCard(); return; }
      var form = findForm();
      if (!form) return;
      if (card && card.isConnected && ui) return;
      mount(form);
    } catch (e) { err('ensure', e); }
  }
  var ensureTimer = null;
  function schedEnsure() { clearTimeout(ensureTimer); ensureTimer = setTimeout(ensure, 200); }

  try {
    restore();
    var mo = new MutationObserver(function (muts) {
      var b = batch;
      if (b) {
        for (var i = 0; i < muts.length; i++) {
          if (!(card && card.contains(muts[i].target))) { b.lastAct = now(); b.mutated = true; break; }
        }
      }
      if (!card || !card.isConnected) schedEnsure();
    });
    mo.observe(document.body, { childList: true, subtree: true, characterData: true });
    ['pushState', 'replaceState'].forEach(function (m) {
      var o = history[m];
      history[m] = function () { var r = o.apply(this, arguments); schedEnsure(); return r; };
    });
    window.addEventListener('popstate', schedEnsure);
    setInterval(ensure, 1500);
    ensure();
    log('ready');
  } catch (e) { err('init failed', e); }
})();
