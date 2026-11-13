'use strict';
/* Развилка — бесконечный холст для ветвящихся сценариев. Без сборки и зависимостей. */
(() => {

// ================= Константы =================
const KINDS = [
  { id: 'scene',  name: 'Сцена',    color: '#5b8def' },
  { id: 'choice', name: 'Выбор',    color: '#e0a43a' },
  { id: 'combat', name: 'Бой',      color: '#e05252' },
  { id: 'dialog', name: 'Диалог',   color: '#9b6be0' },
  { id: 'check',  name: 'Проверка', color: '#3aa6a0' },
  { id: 'loot',   name: 'Награда',  color: '#5fb85f' },
  { id: 'ending', name: 'Концовка', color: '#8a8f98' },
];
const KIND = Object.fromEntries(KINDS.map(k => [k.id, k]));
const CALLOUTS = {
  remark: { name: 'Ремарка',          color: '#f0c060' },
  read:   { name: 'Зачитать игрокам', color: '#5b8def' },
  warn:   { name: 'Важно',            color: '#e05a5a' },
  check:  { name: 'Проверка',         color: '#3aa6a0' },
};
const FONTS = [
  { id: 'sans',  name: 'Обычный',      css: 'system-ui,-apple-system,"Segoe UI",Roboto,sans-serif' },
  { id: 'serif', name: 'С засечками',  css: 'Georgia,"Times New Roman",serif' },
  { id: 'mono',  name: 'Моноширинный', css: 'ui-monospace,Consolas,"Courier New",monospace' },
  { id: 'hand',  name: 'Рукописный',   css: '"Segoe Print","Comic Sans MS","Bradley Hand",cursive' },
];
const FONT = Object.fromEntries(FONTS.map(f => [f.id, f]));
const TEXT_COLORS = ['#e6e8ec', '#9aa1ad', '#1d1f24', '#f0c060', '#f08a5d', '#e05a5a', '#e86fb0', '#a78bfa', '#5b8def', '#3fb8af', '#6cc070'];
const ZONE_COLORS = ['#f0c060', '#6cc070', '#5b8def', '#e86fb0', '#a78bfa', '#f08a5d', '#e05a5a', '#9aa1ad'];
const NOTE_COLORS = ['#f3d36b', '#9be08a', '#8fc1ff', '#ffadd2', '#c9b6ff', '#ffbf8a', '#e8e8e8'];
const TEXT_TYPES = new Set(['card', 'text', 'note', 'callout']);
const LINKABLE = new Set(['card', 'text', 'note', 'callout', 'image']);
const APP_VERSION = '1.1.1'; // версия Развилки — менять вместе с desktop/src-tauri/tauri.conf.json
const MIN_S = 0.08, MAX_S = 3;
const MOBILE = matchMedia('(pointer: coarse)').matches && Math.min(screen.width, screen.height) < 820;
if (MOBILE) document.body.classList.add('mobile');
// приложение для ПК (Tauri) — см. раздел «Приложение для ПК» ниже
const DESKTOP = !!(window.__TAURI_INTERNALS__ || window.__TAURI__);
const tauriInvoke = (cmd, args) => (window.__TAURI__?.core?.invoke || window.__TAURI_INTERNALS__.invoke)(cmd, args);
if (DESKTOP) document.body.classList.add('desktop');
const BK_KEY = 'razvilka.backupDir';
let backupDir = ''; try { backupDir = DESKTOP ? localStorage.getItem(BK_KEY) || '' : ''; } catch {}
let backupTimer = null, lastBackupAt = null;

const $ = (s, r = document) => r.querySelector(s);
const SVGNS = 'http://www.w3.org/2000/svg';
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const r1 = v => Math.round(v * 10) / 10;
const plainOK = (() => { const d = document.createElement('div'); d.contentEditable = 'plaintext-only'; return d.contentEditable === 'plaintext-only'; })();

const viewport = $('#viewport'), world = $('#world'), svg = $('#edges'), edgeLayer = $('#edgeLayer'),
  tempEdge = $('#tempEdge'), itemLayer = $('#itemLayer'), zoneLayer = $('#zoneLayer'), selbox = $('#selbox');

// ================= Хранилище (IndexedDB) =================
const mem = { meta: new Map(), boards: new Map() };
const DB = {
  db: null,
  open() {
    return new Promise((res, rej) => {
      const r = indexedDB.open('razvilka', 1);
      r.onupgradeneeded = () => { const d = r.result; d.createObjectStore('meta', { keyPath: 'id' }); d.createObjectStore('boards', { keyPath: 'id' }); };
      r.onsuccess = () => { this.db = r.result; res(); };
      r.onerror = () => rej(r.error);
    });
  },
  run(store, mode, fn) {
    if (!this.db) return Promise.resolve(fn(null));
    return new Promise((res, rej) => {
      const t = this.db.transaction(store, mode); const req = fn(t.objectStore(store));
      t.oncomplete = () => res(req && req.result); t.onerror = () => rej(t.error); t.onabort = () => rej(t.error);
    });
  },
  get(st, id) { return this.db ? this.run(st, 'readonly', s => s.get(id)) : Promise.resolve(structuredClone(mem[st].get(id))); },
  put(st, v)  { if (!this.db) { mem[st].set(v.id, structuredClone(v)); return Promise.resolve(); } return this.run(st, 'readwrite', s => s.put(v)); },
  del(st, id) { if (!this.db) { mem[st].delete(id); return Promise.resolve(); } return this.run(st, 'readwrite', s => s.delete(id)); },
  all(st)     { return this.db ? this.run(st, 'readonly', s => s.getAll()) : Promise.resolve([...mem[st].values()]); },
};

// ================= Состояние =================
let ws = null;                    // { id:'ws', folders:[], boards:[], current }
let boardId = null;
const items = new Map();          // id -> item
const edges = new Map();          // id -> edge
const adj = new Map();            // itemId -> Set(edgeId)
const view = { x: 0, y: 0, s: 1 };
const selected = new Set();
let selEdge = null;
let boxMode = false;
let maxZ = 0;
const itemEls = new Map(), edgeEls = new Map();
let editing = null;
const revealed = new Set(); // открытые спойлеры — только на этот сеанс, после перезапуска снова скрыты
let lastPointer = null;           // последняя позиция курсора на холсте (экран)
let searchSet = new Set(), searchHits = [], searchIdx = -1;

// ================= Модель =================
function defaults(type) {
  const base = { font: 'sans', size: 14, color: null, bold: false, italic: false, underline: false, align: 'left' };
  switch (type) {
    case 'card':    return { ...base, w: 250, h: 90, kind: 'scene', title: '', text: '' };
    case 'text':    return { ...base, w: 280, h: 30, size: 18, text: '' };
    case 'note':    return { ...base, w: 210, h: 120, bg: NOTE_COLORS[0], text: '' };
    case 'callout': return { ...base, w: 280, h: 70, variant: 'remark', text: '' };
    case 'zone':    return { w: 520, h: 340, color: ZONE_COLORS[0], label: '' };
    case 'image':   return { w: 320, h: 220, src: '' };
  }
}
function addItem(type, x, y, props = {}) {
  const it = { id: uid(), type, ...defaults(type), x: Math.round(x), y: Math.round(y), ...props, z: ++maxZ, _v: 1 };
  if (type === 'zone') it.z = -1e6 + it.z; // зоны всегда под всем
  items.set(it.id, it); dirty(); return it;
}
function adjAdd(e) { for (const id of [e.from, e.to]) { let s = adj.get(id); if (!s) adj.set(id, s = new Set()); s.add(e.id); } }
function adjDel(e) { adj.get(e.from)?.delete(e.id); adj.get(e.to)?.delete(e.id); }
function addEdge(from, to, label = '', extra) {
  if (from === to) return null;
  for (const id of adj.get(from) || []) { const e = edges.get(id); if (e.from === from && e.to === to) { if (extra) Object.assign(e, extra); return e; } }
  const e = { id: uid(), from, to, label, ...(extra || {}) }; edges.set(e.id, e); adjAdd(e); dirty(); return e;
}
const edgeExtra = e => (e.kind ? { kind: e.kind, anchor: e.anchor, anchorText: e.anchorText } : undefined);
function removeEdge(id) { const e = edges.get(id); if (!e) return; adjDel(e); edges.delete(id); if (selEdge === id) selEdge = null; }
function removeItem(id) {
  for (const eid of [...(adj.get(id) || [])]) removeEdge(eid);
  items.delete(id); adj.delete(id); selected.delete(id);
  if (editing && editing.id === id) editing = null;
}
const touch = it => { it._v = (it._v || 0) + 1; };
function clean(it) { const o = { ...it }; delete o._v; delete o._paraY; return o; }

function loadData(its, eds) {
  items.clear(); edges.clear(); adj.clear(); maxZ = 0;
  for (const raw of its || []) {
    if (!raw || !raw.id || !defaults(raw.type)) continue;
    const it = { ...defaults(raw.type), ...raw, _v: 1 };
    it.x = +it.x || 0; it.y = +it.y || 0; it.w = +it.w || 200; it.h = +it.h || 60;
    items.set(it.id, it); if (it.type !== 'zone') maxZ = Math.max(maxZ, it.z || 0);
  }
  for (const e of eds || []) if (e && items.has(e.from) && items.has(e.to) && e.from !== e.to) { edges.set(e.id, { label: '', ...e }); adjAdd(edges.get(e.id)); }
  for (const el of itemEls.values()) el.remove(); itemEls.clear();
  for (const el of edgeEls.values()) el.remove(); edgeEls.clear();
}

// ================= Отмена / повтор =================
const undoStack = [], redoStack = [];
const snap = () => JSON.stringify({ i: [...items.values()].map(clean), e: [...edges.values()] });
function pushUndo(s) { undoStack.push(s); if (undoStack.length > 150) undoStack.shift(); redoStack.length = 0; updateUI(); }
function commit() { pushUndo(snap()); }
function applySnap(str) { const d = JSON.parse(str); loadData(d.i, d.e); }
function undo() { stopEdit(); if (!undoStack.length) return; redoStack.push(snap()); applySnap(undoStack.pop()); afterHistory(); }
function redo() { stopEdit(); if (!redoStack.length) return; undoStack.push(snap()); applySnap(redoStack.pop()); afterHistory(); }
function afterHistory() {
  for (const id of [...selected]) if (!items.has(id)) selected.delete(id);
  if (selEdge && !edges.has(selEdge)) selEdge = null;
  dirty(); updateUI();
}

// ================= Сохранение =================
let lastSavedAt = null;
let saveTimer = null, contentChanged = false, saving = false, saveAgain = false;
const saveState = $('#saveState');
function setSaveState(t, cls) { saveState.textContent = t; saveState.className = cls || ''; }
function dirty() { contentChanged = true; setSaveState('Сохранение…', 'busy'); scheduleSave(); schedule(); }
function scheduleSave(ms = 300) { clearTimeout(saveTimer); saveTimer = setTimeout(saveNow, ms); }
async function saveNow() {
  clearTimeout(saveTimer); saveTimer = null;
  if (!boardId) return;
  if (saving) { saveAgain = true; return; }
  saving = true;
  try {
    const content = contentChanged; contentChanged = false;
    if (content) {
      await DB.put('boards', { id: boardId, items: [...items.values()].map(clean), edges: [...edges.values()], view: { ...view } });
      const b = ws.boards.find(b => b.id === boardId); if (b) b.updated = Date.now();
      await saveWs();
      bc?.postMessage({ type: 'saved', tab: TAB, board: boardId });
      scheduleBackup();
    } else {
      // сдвинули или приблизили холст — пишем только вид, чтобы не затереть правки из другого окна
      const cur = await DB.get('boards', boardId);
      if (cur) { cur.view = { ...view }; await DB.put('boards', cur); }
    }
    setSaveState(DB.db ? 'Сохранено' : 'Не сохраняется!', DB.db ? '' : 'err'); lastSavedAt = new Date();
  } catch (err) { setSaveState('Ошибка сохранения', 'err'); toast('Не удалось сохранить: ' + err.message); }
  saving = false;
  if (saveAgain) { saveAgain = false; saveNow(); }
}
const saveWs = () => DB.put('meta', ws).then(() => bc?.postMessage({ type: 'saved', tab: TAB, ws: true }));
const flush = () => { if (editing) syncEditText(); if (saveTimer || contentChanged) saveNow(); };
document.addEventListener('visibilitychange', () => { if (document.hidden) flush(); });
window.addEventListener('pagehide', flush);

// Несколько вкладок/окон: после сохранения сообщаем остальным, они подтягивают свежую версию.
const bc = 'BroadcastChannel' in window ? new BroadcastChannel('razvilka') : null;
const TAB = uid();
let paused = false;
if (bc) bc.onmessage = async ({ data }) => {
  if (!data || data.tab === TAB || paused) return;
  if (data.type === 'saved') {
    if (data.ws) { const fresh = await DB.get('meta', 'ws'); if (fresh) { ws = fresh; ws.current = boardId; renderTree(); renderCrumb(); } }
    if (data.board === boardId && !saveTimer && !editing && !G) {
      const d = await DB.get('boards', boardId); if (!d) return;
      loadData(d.items, d.edges);
      for (const id of [...selected]) if (!items.has(id)) selected.delete(id);
      if (selEdge && !edges.has(selEdge)) selEdge = null;
      updateUI(); schedule();
    }
  }
};
function pause() { flush(); paused = true; boardId = null; $('#detached').classList.remove('hidden'); }

// ================= Отрисовка =================
let rq = false, lod = null;
function schedule() { if (!rq) { rq = true; requestAnimationFrame(render); } }

function makeEl(it) {
  const el = document.createElement('div');
  el.className = 'item ' + it.type; el.dataset.id = it.id;
  const ph = MOBILE ? 'Нажмите дважды, чтобы писать' : 'Двойной клик — писать';
  switch (it.type) {
    case 'card': el.innerHTML = `<div class="ckind"></div><div class="ctitle" data-f="title" data-ph="Название сцены"></div><div class="ctext" data-f="text" data-ph="＋ описание, заметки ДМ…"></div>`; break;
    case 'text': el.innerHTML = `<div data-f="text" data-ph="Текст"></div>`; break;
    case 'note': el.innerHTML = `<div data-f="text" data-ph="Заметка"></div>`; break;
    case 'callout': el.innerHTML = `<div class="chead"></div><div data-f="text" data-ph="${ph}"></div>`; break;
    case 'zone': el.innerHTML = `<div class="zlabel" data-f="label" data-ph="Зона"></div>`; break;
    case 'image': el.innerHTML = `<img alt="" referrerpolicy="no-referrer" draggable="false" decoding="async"><div class="ph"><span class="ph-text">Загрузка…</span><button class="img-retry" type="button" hidden>↻ Загрузить снова</button></div>`;
      { const img = el.querySelector('img'), ph2 = el.querySelector('.ph'), txt = ph2.querySelector('.ph-text'), rb = ph2.querySelector('.img-retry');
        img.onload = () => { ph2.hidden = true; el._tries = 0; };
        img.onerror = () => {
          if (!img.getAttribute('src')) return;
          el._tries = (el._tries || 0) + 1;
          if (el._tries === 1) { setTimeout(() => retryImage(el), 1500); return; } // одна тихая повторная попытка
          ph2.hidden = false; txt.textContent = 'Картинка не загрузилась'; rb.hidden = false;
        }; }
      break;
  }
  if (LINKABLE.has(it.type)) el.insertAdjacentHTML('beforeend', '<div class="port" title="Потяните, чтобы создать переход"></div>');
  if (it.type !== 'zone') el.insertAdjacentHTML('beforeend', '<div class="spo"><button class="spo-btn" type="button">🔒 Спойлер — показать</button></div><button class="spo-hide" type="button" title="Снова скрыть (H — скрыть все)">🔒</button>');
  if (it.type === 'zone') el.insertAdjacentHTML('beforeend', ['n', 's', 'e', 'w', 'nw', 'ne', 'sw', 'se'].map(d => `<div class="zh zh-${d}" data-h="${d}"></div>`).join(''));
  else el.insertAdjacentHTML('beforeend', '<div class="rs" data-h="se" title="Размер"></div>');
  el._v = -1;
  return el;
}

// Повторная загрузка картинки: сначала тот же адрес заново, потом — с меткой против кэша
function retryImage(el) {
  const it = items.get(el.dataset.id); if (!it || !it.src) return;
  const img = el.querySelector('img'), ph = el.querySelector('.ph');
  ph.hidden = false; ph.querySelector('.ph-text').textContent = 'Загрузка…'; ph.querySelector('.img-retry').hidden = true;
  const bust = (el._tries || 0) >= 2 ? (it.src.includes('?') ? '&' : '?') + '_r=' + Date.now() : '';
  img.removeAttribute('src');
  requestAnimationFrame(() => { img.src = it.src + bust; });
}
function applyTextStyle(f, it) {
  f.style.fontFamily = (FONT[it.font] || FONTS[0]).css;
  f.style.fontSize = it.size + 'px';
  f.style.fontWeight = it.bold ? '700' : '';
  f.style.fontStyle = it.italic ? 'italic' : '';
  f.style.textDecoration = it.underline ? 'underline' : '';
  f.style.textAlign = it.align;
  f.style.color = it.color || '';
}

function fill(el, it) {
  el.style.width = it.w + 'px';
  el.style.zIndex = it.z;
  el.classList.toggle('spoiler', !!it.spoiler);
  el.classList.toggle('revealed', !!it.spoiler && revealed.has(it.id));
  const isEditing = editing && editing.id === it.id;
  const setF = (name, val) => { const f = el.querySelector(`[data-f="${name}"]`); if (f && !(isEditing && editing.field === name)) f.textContent = val || ''; return f; };
  switch (it.type) {
    case 'card': {
      const k = KIND[it.kind] || KINDS[0];
      el.style.setProperty('--c', k.color);
      el.querySelector('.ckind').textContent = k.name;
      setF('title', it.title); applyTextStyle(setF('text', it.text), it);
      break;
    }
    case 'text': applyTextStyle(setF('text', it.text), it); break;
    case 'note': el.style.setProperty('--nb', it.bg); applyTextStyle(setF('text', it.text), it); break;
    case 'callout': {
      const c = CALLOUTS[it.variant] || CALLOUTS.remark;
      el.style.setProperty('--cc', c.color); el.querySelector('.chead').textContent = c.name;
      for (const v of Object.keys(CALLOUTS)) el.classList.toggle('v-' + v, v === it.variant);
      applyTextStyle(setF('text', it.text), it);
      break;
    }
    case 'zone': el.style.setProperty('--zc', it.color); el.style.height = it.h + 'px'; setF('label', it.label); break;
    case 'image': {
      el.style.height = it.h + 'px';
      const img = el.querySelector('img');
      if (img.getAttribute('src') !== it.src && !(img.getAttribute('src') || '').startsWith(it.src)) {
        const ph = el.querySelector('.ph'); ph.hidden = false; ph.querySelector('.ph-text').textContent = 'Загрузка…'; ph.querySelector('.img-retry').hidden = true;
        el._tries = 0; img.src = it.src;
      }
      break;
    }
  }
}

function render() {
  rq = false;
  const s = view.s;
  world.style.transform = `translate(${view.x}px,${view.y}px) scale(${s})`;
  const nl = s < 0.4; if (nl !== lod) { lod = nl; world.classList.toggle('lod', lod); for (const el of itemEls.values()) el._v = -1; }
  let g = 24 * s; while (g < 12) g *= 4;
  viewport.style.backgroundSize = `${g}px ${g}px`;
  viewport.style.backgroundPosition = `${view.x}px ${view.y}px`;
  $('#empty').hidden = items.size > 0;

  const vw = viewport.clientWidth, vh = viewport.clientHeight;
  const mx = vw * 0.5 / s, my = vh * 0.5 / s;
  const x0 = -view.x / s - mx, y0 = -view.y / s - my, x1 = (vw - view.x) / s + mx, y1 = (vh - view.y) / s + my;

  const seen = new Set(), measure = [];
  for (const it of items.values()) {
    if (it.x + it.w < x0 || it.x > x1 || it.y + it.h < y0 || it.y > y1) continue;
    seen.add(it.id);
    let el = itemEls.get(it.id);
    if (!el) { el = makeEl(it); itemEls.set(it.id, el); (it.type === 'zone' ? zoneLayer : itemLayer).appendChild(el); }
    if (el._v !== it._v) { fill(el, it); el._v = it._v; if (TEXT_TYPES.has(it.type)) measure.push(it); }
    if (el._x !== it.x || el._y !== it.y) { el.style.transform = `translate(${it.x}px,${it.y}px)`; el._x = it.x; el._y = it.y; }
    const sel = selected.has(it.id); if (el._sel !== sel) { el.classList.toggle('sel', sel); el._sel = sel; if (it.type === 'card') measure.push(it); }
    const fd = searchSet.has(it.id); if (el._fd !== fd) { el.classList.toggle('found', fd); el._fd = fd; }
  }
  for (const [id, el] of itemEls) if (!seen.has(id)) { el.remove(); itemEls.delete(id); }
  if (editing && editing.measure) { const it = items.get(editing.id); if (it) measure.push(it); editing.measure = false; }
  for (const it of measure) {
    const el = itemEls.get(it.id); if (!el) continue;
    const h = el.offsetHeight; if (h && h !== it.h) it.h = h;
    if (it.type === 'card') it._paraY = lod ? null : paraYFromEl(el, it, view.s);
  }

  // размеры svg под содержимое
  let bx0 = Infinity, by0 = Infinity, bx1 = -Infinity, by1 = -Infinity;
  for (const it of items.values()) {
    if (it.x < bx0) bx0 = it.x; if (it.y < by0) by0 = it.y;
    if (it.x + it.w > bx1) bx1 = it.x + it.w; if (it.y + it.h > by1) by1 = it.y + it.h;
  }
  if (G && G.type === 'link') { bx0 = Math.min(bx0, G.pt.x); by0 = Math.min(by0, G.pt.y); bx1 = Math.max(bx1, G.pt.x); by1 = Math.max(by1, G.pt.y); }
  if (bx0 === Infinity) { bx0 = by0 = 0; bx1 = by1 = 10; }
  bx0 -= 400; by0 -= 400; bx1 += 400; by1 += 400;
  const vb = `${bx0} ${by0} ${bx1 - bx0} ${by1 - by0}`;
  if (vb !== svg._vb) {
    svg.setAttribute('viewBox', vb);
    Object.assign(svg.style, { left: bx0 + 'px', top: by0 + 'px', width: (bx1 - bx0) + 'px', height: (by1 - by0) + 'px' });
    svg._vb = vb;
  }

  const eseen = new Set();
  for (const e of edges.values()) {
    const a = items.get(e.from), b = items.get(e.to);
    if (Math.max(a.x + a.w, b.x + b.w) < x0 || Math.min(a.x, b.x) > x1 || Math.max(a.y + a.h, b.y + b.h) < y0 || Math.min(a.y, b.y) > y1) continue;
    eseen.add(e.id);
    let gEl = edgeEls.get(e.id);
    if (!gEl) { gEl = makeEdgeEl(e.id); edgeEls.set(e.id, gEl); edgeLayer.appendChild(gEl); }
    const pin = e.kind === 'pin';
    const geo = pin ? pinGeo(a, b, e) : edgeGeo(a, b);
    if (gEl._pin !== pin) { gEl.classList.toggle('pin', pin); gEl._pin = pin; gEl._sel = null; }
    if (gEl._d !== geo.d) { gEl._hit.setAttribute('d', geo.d); gEl._line.setAttribute('d', geo.d); gEl._d = geo.d; }
    if (gEl._lab !== e.label || gEl._mx !== geo.mx || gEl._my !== geo.my) {
      gEl._text.textContent = e.label; gEl._text.setAttribute('x', geo.mx); gEl._text.setAttribute('y', geo.my);
      gEl._lab = e.label; gEl._mx = geo.mx; gEl._my = geo.my;
    }
    const sel = selEdge === e.id;
    if (gEl._sel !== sel) { gEl.classList.toggle('sel', sel); gEl._line.setAttribute('marker-end', sel ? 'url(#arrowSel)' : pin ? 'url(#arrowPin)' : 'url(#arrow)'); gEl._sel = sel; }
  }
  for (const [id, el] of edgeEls) if (!eseen.has(id)) { el.remove(); edgeEls.delete(id); }

  if (G && G.type === 'link') {
    const a = items.get(G.from), t = G.over && items.get(G.over);
    tempEdge.setAttribute('d', t ? edgeGeo(a, t).d : tempGeo(a, G.pt));
  } else tempEdge.setAttribute('d', '');
}

function makeEdgeEl(id) {
  const g = document.createElementNS(SVGNS, 'g'); g.setAttribute('class', 'edge'); g.dataset.id = id;
  const hit = document.createElementNS(SVGNS, 'path'); hit.setAttribute('class', 'hit');
  const line = document.createElementNS(SVGNS, 'path'); line.setAttribute('class', 'line'); line.setAttribute('marker-end', 'url(#arrow)');
  const text = document.createElementNS(SVGNS, 'text'); text.setAttribute('class', 'elabel');
  g.append(hit, line, text); g._hit = hit; g._line = line; g._text = text;
  return g;
}

function edgeGeo(a, b) {
  const acx = a.x + a.w / 2, acy = a.y + a.h / 2, bcx = b.x + b.w / 2, bcy = b.y + b.h / 2;
  const dx = bcx - acx, dy = bcy - acy;
  const gapX = Math.abs(dx) - (a.w + b.w) / 2, gapY = Math.abs(dy) - (a.h + b.h) / 2;
  let p1x, p1y, p2x, p2y, c1x, c1y, c2x, c2y;
  if (gapX >= gapY) {
    const sx = dx >= 0 ? 1 : -1;
    p1x = acx + sx * a.w / 2; p1y = acy; p2x = bcx - sx * b.w / 2; p2y = bcy;
    const k = Math.max(40, Math.abs(p2x - p1x) / 2);
    c1x = p1x + sx * k; c1y = p1y; c2x = p2x - sx * k; c2y = p2y;
  } else {
    const sy = dy >= 0 ? 1 : -1;
    p1x = acx; p1y = acy + sy * a.h / 2; p2x = bcx; p2y = bcy - sy * b.h / 2;
    const k = Math.max(40, Math.abs(p2y - p1y) / 2);
    c1x = p1x; c1y = p1y + sy * k; c2x = p2x; c2y = p2y - sy * k;
  }
  return {
    d: `M${r1(p1x)},${r1(p1y)} C${r1(c1x)},${r1(c1y)} ${r1(c2x)},${r1(c2y)} ${r1(p2x)},${r1(p2y)}`,
    mx: r1((p1x + 3 * c1x + 3 * c2x + p2x) / 8), my: r1((p1y + 3 * c1y + 3 * c2y + p2y) / 8),
  };
}
function tempGeo(a, p) {
  const acx = a.x + a.w / 2, acy = a.y + a.h / 2, sx = p.x >= acx ? 1 : -1;
  const p1x = acx + sx * a.w / 2, k = Math.max(40, Math.abs(p.x - p1x) / 2);
  return `M${r1(p1x)},${r1(acy)} C${r1(p1x + sx * k)},${r1(acy)} ${r1(p.x - sx * k)},${r1(p.y)} ${r1(p.x)},${r1(p.y)}`;
}

// ================= Координаты и вид =================
const vpPoint = e => { const r = viewport.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top }; };
const toWorld = p => ({ x: (p.x - view.x) / view.s, y: (p.y - view.y) / view.s });
function viewChanged() { schedule(); scheduleSave(600); }
function zoomAt(px, py, ns) {
  ns = clamp(ns, MIN_S, MAX_S);
  const wx = (px - view.x) / view.s, wy = (py - view.y) / view.s;
  view.s = ns; view.x = px - wx * ns; view.y = py - wy * ns; viewChanged();
}
function centerOn(it) {
  const vw = viewport.clientWidth, vh = viewport.clientHeight;
  view.x = vw / 2 - (it.x + it.w / 2) * view.s;
  view.y = vh * 0.45 - (it.y + it.h / 2) * view.s;
  viewChanged();
}
function fit() {
  const vw = viewport.clientWidth, vh = viewport.clientHeight;
  if (!items.size) { view.s = 1; view.x = vw / 2; view.y = vh / 2; viewChanged(); return; }
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const it of items.values()) { x0 = Math.min(x0, it.x); y0 = Math.min(y0, it.y - 20); x1 = Math.max(x1, it.x + it.w); y1 = Math.max(y1, it.y + it.h); }
  const top = $('#toolbar').offsetHeight + 16, pad = 40;
  const left = !MOBILE && !sidebar.classList.contains('hidden') ? sidebar.offsetWidth + 16 : 0;
  const aw = vw - left;
  const s = clamp(Math.min((aw - pad * 2) / (x1 - x0), (vh - top - pad * 2) / (y1 - y0)), MIN_S, 1.2);
  view.s = s; view.x = left + (aw - (x1 - x0) * s) / 2 - x0 * s; view.y = top + (vh - top - (y1 - y0) * s) / 2 - y0 * s;
  viewChanged();
}
function viewCenterWorld() {
  const p = lastPointer || { x: viewport.clientWidth / 2, y: viewport.clientHeight * 0.45 };
  return toWorld(p);
}

// ================= Указатель (мышь + касания) =================
const ptrs = new Map();
let G = null;               // текущий жест
let lastTap = null;
const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const mid = (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 });

function isDoubleTap(p, key) {
  const now = performance.now();
  const ok = lastTap && lastTap.key === key && now - lastTap.t < 380 && Math.hypot(p.x - lastTap.x, p.y - lastTap.y) < 30;
  lastTap = ok ? null : { t: now, x: p.x, y: p.y, key };
  return ok;
}
function canMove(it) { return !MOBILE || TEXT_TYPES.has(it.type); }

viewport.addEventListener('pointerdown', e => {
  const t = e.target;
  const rmb = e.pointerType === 'mouse' && e.button === 2;
  if (rmb && (MOBILE || ptrs.size)) return;
  // клик внутри редактируемого текста — отдаём браузеру
  if (editing && editing.el.contains(t)) return;
  // телефон / узкое окно: тап по холсту закрывает боковую панель
  if ((MOBILE || innerWidth < 760) && !sidebar.classList.contains('hidden')) { toggleSidebar(false); return; }
  if (t.closest && t.closest('.img-retry')) { const el = t.closest('.item'); if (el) { el._tries = 2; retryImage(el); } return; }
  hideMenu(); hideSwatches();
  const p = vpPoint(e); ptrs.set(e.pointerId, p); lastPointer = p;
  try { viewport.setPointerCapture(e.pointerId); } catch {}
  if (editing) stopEdit();

  if (ptrs.size === 2) {
    cancelGesture();
    const [a, b] = [...ptrs.values()];
    G = { type: 'pinch', d0: dist(a, b) || 1, m0: mid(a, b), s0: view.s, vx0: view.x, vy0: view.y };
    return;
  }
  if (ptrs.size > 2) return;
  if (e.pointerType === 'mouse' && e.button === 1) { e.preventDefault(); G = { type: 'pan', start: p, last: p, mid: true, moved: true }; viewport.classList.add('panning'); return; }
  if (rmb) { G = { type: 'box', start: p, cur: p, add: e.shiftKey || e.ctrlKey }; return; } // зажатая ПКМ — рамка выделения

  const itemEl = t.closest('.item');
  const id = itemEl && itemEl.dataset.id, it = id && items.get(id);
  if (it && t.closest('.spo-btn')) { setRevealed(it, true); ptrs.delete(e.pointerId); return; }
  if (it && t.closest('.spo-hide')) { setRevealed(it, false); ptrs.delete(e.pointerId); return; }
  if (it && t.closest('.port')) { G = { type: 'link', from: id, start: p, pt: toWorld(p), over: null, moved: false }; return; }
  const handle = it && t.closest('[data-h]');
  if (handle) {
    commit();
    G = { type: 'resize', it, dir: handle.dataset.h, start: p, x0: it.x, y0: it.y, w0: it.w, h0: it.h, ar: it.h / it.w };
    if (!selected.has(id)) { selected.clear(); selected.add(id); selEdge = null; selChanged(); }
    return;
  }
  if (it && (it.type !== 'zone' || t.closest('.zlabel'))) {
    if (MOBILE && !TEXT_TYPES.has(it.type)) { G = { type: 'pan', start: p, vx0: view.x, vy0: view.y, moved: false }; return; }
    selEdge = null;
    const wasSel = selected.size === 1 && selected.has(id) && !(e.shiftKey || e.ctrlKey || e.metaKey);
    if (e.shiftKey || e.ctrlKey || e.metaKey) { selected.has(id) ? selected.delete(id) : selected.add(id); }
    else if (!selected.has(id)) { selected.clear(); selected.add(id); }
    selChanged();
    G = { type: 'move', id, start: p, moved: false, wasSel, field: t.closest('[data-f]')?.dataset.f || null };
    return;
  }
  const edgeEl = !MOBILE && t.closest('.edge');
  if (edgeEl) { G = { type: 'edge', id: edgeEl.dataset.id, start: p, vx0: view.x, vy0: view.y, moved: false }; return; }
  if (!MOBILE && (boxMode || e.shiftKey)) { G = { type: 'box', start: p, cur: p, add: e.shiftKey }; return; }
  G = { type: 'pan', start: p, vx0: view.x, vy0: view.y, moved: false };
});

viewport.addEventListener('pointermove', e => {
  const p = vpPoint(e);
  if (e.pointerType === 'mouse') lastPointer = p;
  if (!ptrs.has(e.pointerId)) return;
  ptrs.set(e.pointerId, p);
  if (!G) return;
  if (G.type === 'pinch') {
    if (ptrs.size < 2) return;
    const [a, b] = [...ptrs.values()], d = dist(a, b), m = mid(a, b);
    const ns = clamp(G.s0 * d / G.d0, MIN_S, MAX_S);
    const wx = (G.m0.x - G.vx0) / G.s0, wy = (G.m0.y - G.vy0) / G.s0;
    view.s = ns; view.x = m.x - wx * ns; view.y = m.y - wy * ns; viewChanged();
    return;
  }
  const dx = p.x - G.start.x, dy = p.y - G.start.y;
  const far = Math.hypot(dx, dy) > (e.pointerType === 'mouse' ? 3 : 8);
  switch (G.type) {
    case 'edge': if (!far) return; G.type = 'pan'; // далее как панорама
    // falls through
    case 'pan':
      // сдвигаем на приращение от прошлого кадра, а не от точки старта:
      // если во время перетаскивания случайно провернулось колесо (масштаб), холст не прыгает
      if (far && !G.moved) { G.moved = true; G.last = G.start; }
      if (G.moved) {
        const l = G.last || G.start;
        viewport.classList.add('panning'); view.x += p.x - l.x; view.y += p.y - l.y; G.last = p; viewChanged();
      }
      return;
    case 'move': {
      if (!G.moved) {
        if (!far) return;
        G.moved = true; commit();
        const list = new Set([...selected].filter(id => items.has(id) && canMove(items.get(id))));
        // зона тащит за собой всё, что целиком внутри неё
        for (const id of [...list]) {
          const z = items.get(id);
          if (z.type !== 'zone') continue;
          for (const o of items.values()) if (o !== z && o.x >= z.x && o.y >= z.y && o.x + o.w <= z.x + z.w && o.y + o.h <= z.y + z.h) list.add(o.id);
        }
        G.orig = [...list].map(id => { const o = items.get(id); return [o, o.x, o.y]; });
      }
      for (const [o, ox, oy] of G.orig) { o.x = Math.round(ox + dx / view.s); o.y = Math.round(oy + dy / view.s); }
      schedule(); return;
    }
    case 'resize': {
      const it = G.it, ddx = dx / view.s, ddy = dy / view.s;
      if (it.type === 'image') { it.w = Math.round(Math.max(40, G.w0 + ddx)); it.h = e.shiftKey ? Math.round(Math.max(30, G.h0 + ddy)) : Math.round(it.w * G.ar); }
      else if (it.type === 'zone') {
        const d = G.dir; let x = G.x0, y = G.y0, w = G.w0, h = G.h0;
        if (d.includes('e')) w = Math.max(80, G.w0 + ddx);
        if (d.includes('w')) { w = Math.max(80, G.w0 - ddx); x = G.x0 + G.w0 - w; }
        if (d.includes('s')) h = Math.max(60, G.h0 + ddy);
        if (d.includes('n')) { h = Math.max(60, G.h0 - ddy); y = G.y0 + G.h0 - h; }
        it.x = Math.round(x); it.y = Math.round(y); it.w = Math.round(w); it.h = Math.round(h);
      }
      else { it.w = Math.round(Math.max(80, G.w0 + ddx)); }
      touch(it); schedule(); return;
    }
    case 'link': {
      G.moved = G.moved || far; G.pt = toWorld(p);
      const el = document.elementFromPoint(e.clientX, e.clientY)?.closest?.('.item');
      let over = el && el.dataset.id !== G.from ? el.dataset.id : null;
      if (over && !LINKABLE.has(items.get(over)?.type)) over = null;
      if (over !== G.over) { if (G.over) itemEls.get(G.over)?.classList.remove('target'); G.over = over; if (over) el.classList.add('target'); }
      schedule(); return;
    }
    case 'box': G.cur = p; drawSelbox(); return;
  }
});

function cancelGesture() {
  if (!G) return;
  if (G.type === 'move' && G.moved) dirty();
  if (G.type === 'resize') dirty();
  if (G.type === 'link' && G.over) itemEls.get(G.over)?.classList.remove('target');
  if (G.type === 'box') selbox.hidden = true;
  viewport.classList.remove('panning');
  G = null; schedule();
}

function onUp(e, cancelled) {
  if (!ptrs.has(e.pointerId)) return;
  const p = ptrs.get(e.pointerId); ptrs.delete(e.pointerId);
  if (!G) return;
  if (G.type === 'pinch' || G.type === 'none') { G = ptrs.size ? { type: 'none' } : null; return; }
  if (cancelled) { cancelGesture(); return; }
  const g = G; G = null; viewport.classList.remove('panning');
  const wp = toWorld(p);
  switch (g.type) {
    case 'pan':
      if (!g.moved) {
        if (isDoubleTap(p, 'bg')) showInsertMenu(p, wp);
        else { selected.clear(); selEdge = null; selChanged(); }
      }
      break;
    case 'edge': selected.clear(); selEdge = g.id; selChanged(); break;
    case 'move':
      if (g.moved) dirty();
      else if (isDoubleTap(p, g.id) || (g.wasSel && g.field)) startEdit(g.id, g.field); // второй клик по выделенному — писать
      break;
    case 'resize': dirty(); break;
    case 'link':
      if (g.over) {
        itemEls.get(g.over)?.classList.remove('target'); commit();
        const src = items.get(g.from), dst = items.get(g.over);
        // от проверки, ремарки или заметки к сцене — стрелка-указатель в абзац, на котором отпустили
        const k = src && dst && src.type !== 'card' && dst.type === 'card' ? paraAtPoint(dst, e.clientX, e.clientY) : null;
        if (k != null) addEdge(g.from, g.over, '', { kind: 'pin', anchor: k, anchorText: paraList(dst.text)[k].trim().slice(0, 40) });
        else addEdge(g.from, g.over);
      }
      else if (g.moved) {
        commit();
        const a = items.get(g.from), right = wp.x >= a.x + a.w / 2;
        const n = addItem('card', right ? wp.x : wp.x - 250, wp.y - 30);
        addEdge(g.from, n.id);
        selected.clear(); selected.add(n.id); selEdge = null; selChanged();
        render(); startEdit(n.id, 'title');
      }
      schedule(); break;
    case 'box': {
      selbox.hidden = true;
      const a = toWorld(g.start), b = toWorld(g.cur);
      const rx0 = Math.min(a.x, b.x), ry0 = Math.min(a.y, b.y), rx1 = Math.max(a.x, b.x), ry1 = Math.max(a.y, b.y);
      if (!g.add) selected.clear();
      for (const it of items.values()) {
        const hit = it.type === 'zone'
          ? it.x >= rx0 && it.y >= ry0 && it.x + it.w <= rx1 && it.y + it.h <= ry1
          : it.x < rx1 && it.x + it.w > rx0 && it.y < ry1 && it.y + it.h > ry0;
        if (hit) selected.add(it.id);
      }
      selEdge = null; selChanged(); break;
    }
  }
}
viewport.addEventListener('pointerup', e => onUp(e, false));
viewport.addEventListener('pointercancel', e => onUp(e, true));
viewport.addEventListener('contextmenu', e => { if (!(editing && editing.el.contains(e.target))) e.preventDefault(); });
document.addEventListener('gesturestart', e => e.preventDefault());

function drawSelbox() {
  const a = G.start, b = G.cur;
  Object.assign(selbox.style, { left: Math.min(a.x, b.x) + 'px', top: Math.min(a.y, b.y) + 'px', width: Math.abs(a.x - b.x) + 'px', height: Math.abs(a.y - b.y) + 'px' });
  selbox.hidden = false;
}

viewport.addEventListener('wheel', e => {
  if (editing && editing.el.contains(e.target) && !e.ctrlKey && !e.shiftKey) return;
  e.preventDefault();
  if (G && G.mid) return; // пока холст тянут зажатым колесом — случайные прокрутки колеса игнорируем
  const k = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? viewport.clientHeight : 1;
  if (e.shiftKey && !e.ctrlKey) {
    // Shift + колесо — прокрутка вверх/вниз (Windows при Shift отдаёт прокрутку как горизонтальную)
    const d = (e.deltaY || e.deltaX) * k;
    view.y -= d * 1.2; viewChanged(); return;
  }
  const p = vpPoint(e);
  zoomAt(p.x, p.y, view.s * Math.exp(-e.deltaY * k * (e.ctrlKey ? 0.01 : 0.0015)));
}, { passive: false });
viewport.addEventListener('mousedown', e => { if (e.button === 1) e.preventDefault(); }); // без автопрокрутки Windows по колесу

window.addEventListener('resize', schedule);

// ================= Редактирование текста прямо на холсте =================
function defaultField(it) { return it.type === 'card' ? (it.title ? 'text' : 'title') : it.type === 'zone' ? 'label' : 'text'; }
function setRevealed(it, on) {
  if (on) revealed.add(it.id); else revealed.delete(it.id);
  touch(it); schedule(); renderFmt();
}
function hideAllSpoilers() {
  let n = 0; for (const id of revealed) { const it = items.get(id); if (it) { touch(it); n++; } }
  revealed.clear(); schedule(); renderFmt();
  if (n) toast('Спойлеры снова скрыты', 1500);
}
function startEdit(id, field) {
  const it = items.get(id); if (!it || it.type === 'image') return;
  if (it.spoiler && !revealed.has(id)) { setRevealed(it, true); return; } // скрытое сначала открываем
  if (MOBILE && it.type === 'zone') return;
  stopEdit();
  const el = itemEls.get(id); if (!el) return;
  field = field || defaultField(it);
  const f = el.querySelector(`[data-f="${field}"]`); if (!f) return;
  f.contentEditable = plainOK ? 'plaintext-only' : 'true';
  el.classList.add('editing');
  editing = { id, field, el: f, snap: snap(), before: it[field] || '', measure: true };
  const caretEnd = () => {
    if (!editing || editing.el !== f) return;
    f.focus();
    const r = document.createRange(); r.selectNodeContents(f); r.collapse(false);
    const sel = getSelection(); sel.removeAllRanges(); sel.addRange(r);
  };
  caretEnd(); setTimeout(caretEnd, 40); // повторно — после того как браузер обработает двойной тап
  if (!selected.has(id) || selected.size > 1) { selected.clear(); selected.add(id); selEdge = null; selChanged(); }
}
function syncEditText() {
  if (!editing) return;
  const it = items.get(editing.id); if (!it) return;
  it[editing.field] = editing.el.innerText.replace(/\n$/, '').replace(/ /g, ' ');
}
function stopEdit() {
  if (!editing) return;
  const ed = editing; syncEditText(); editing = null;
  ed.el.contentEditable = 'false';
  ed.el.closest('.item')?.classList.remove('editing');
  const it = items.get(ed.id);
  if (it) {
    if ((it[ed.field] || '') !== ed.before) { pushUndo(ed.snap); dirty(); }
    touch(it); schedule();
  }
  getSelection()?.removeAllRanges();
}
document.addEventListener('input', e => {
  if (!editing || !editing.el.contains(e.target)) return;
  syncEditText(); editing.measure = true; contentChanged = true; setSaveState('Сохранение…', 'busy'); scheduleSave(800); schedule();
});
document.addEventListener('keydown', e => {
  if (!editing) return;
  if (e.key === 'Escape') { e.preventDefault(); e.stopPropagation(); stopEdit(); }
  else if (e.key === 'Enter' && editing.field !== 'text' && !e.shiftKey) {
    e.preventDefault(); e.stopPropagation();
    const { id, field } = editing; stopEdit();
    if (field === 'title') startEdit(id, 'text');
  }
}, true);

// ================= Создание =================
function createAt(type, wp, props = {}) {
  commit();
  const d = defaults(type);
  const it = addItem(type, wp.x - (type === 'zone' ? 0 : d.w / 2), wp.y - (type === 'zone' ? 0 : 20), props);
  selected.clear(); selected.add(it.id); selEdge = null; selChanged();
  render(); startEdit(it.id, type === 'zone' ? 'label' : null);
  return it;
}
const INSERTS = [
  { type: 'card', label: 'Сцена', key: 'C', mk: KIND.scene.color },
  { type: 'text', label: 'Текст', key: 'T', mk: '#e6e8ec', mobile: true },
  { type: 'note', label: 'Заметка', key: 'N', mk: NOTE_COLORS[0], mobile: true },
  { type: 'callout', label: 'Ремарка', key: 'R', mk: CALLOUTS.remark.color, props: { variant: 'remark' }, mobile: true },
  { type: 'callout', label: 'Зачитать игрокам', mk: CALLOUTS.read.color, props: { variant: 'read' }, mobile: true },
  { type: 'callout', label: 'Важно', mk: CALLOUTS.warn.color, props: { variant: 'warn' }, mobile: true },
  { type: 'callout', label: 'Проверка / спасбросок', key: 'K', mk: CALLOUTS.check.color, props: { variant: 'check' }, mobile: true },
  { type: 'zone', label: 'Зона-выделение', key: 'Z', mk: ZONE_COLORS[2] },
  { type: 'image', label: 'Картинка по ссылке', key: 'I', mk: '#9aa1ad' },
];
function showInsertMenu(p, wp) {
  const list = INSERTS.filter(x => !MOBILE || x.mobile);
  showMenu(p.x, p.y, list.map(x => ({
    label: x.label, mk: x.mk, key: MOBILE ? '' : x.key || '',
    fn: () => x.type === 'image' ? askImage(wp) : createAt(x.type, x.type === 'zone' ? { x: wp.x - 40, y: wp.y - 30 } : wp, x.props),
  })), 'Добавить');
}

// ================= Картинки по ссылке =================
function askImage(wp) {
  popAsk({ anchor: lastPointer ? { left: lastPointer.x, right: lastPointer.x, top: lastPointer.y, bottom: lastPointer.y, width: 0, height: 0 } : null,
    title: 'Картинка по ссылке', placeholder: 'https://… — адрес изображения', ok: 'Вставить',
    message: 'Правой кнопкой по картинке → «Копировать адрес изображения»' }).then(r => { if (r) addImageFromUrl(r.value, wp); });
}
function addImageFromUrl(url, wp) {
  if (/^data:image\//i.test(url)) { toast('Это встроенная картинка, а не ссылка. Откройте картинку крупно или на сайте-источнике и скопируйте её адрес.'); return; }
  if (!/^https?:\/\//i.test(url)) { toast('Нужна ссылка, начинающаяся с http:// или https://'); return; }
  toast('Загружаю картинку…', 1500);
  const img = new Image(); img.referrerPolicy = 'no-referrer';
  let done = false;
  const fail = () => {
    if (done) return; done = true;
    if (/pinterest\.[a-z.]+\/pin\//i.test(url) || /pin\.it\//i.test(url)) toast('Это ссылка на страницу пина. Нажмите на картинку правой кнопкой (или удерживайте на телефоне) → «Копировать адрес изображения».', 6000);
    else toast('По ссылке не найдена картинка. Скопируйте именно адрес изображения.', 4500);
  };
  const timer = setTimeout(fail, 15000);
  img.onerror = () => { clearTimeout(timer); fail(); };
  img.onload = () => {
    clearTimeout(timer); if (done) return; done = true;
    const nw = img.naturalWidth || 400, nh = img.naturalHeight || 300;
    const w = Math.min(nw, 420), h = Math.round(w * nh / nw);
    commit();
    const it = addItem('image', wp.x - w / 2, wp.y - h / 2, { w, h, src: url });
    selected.clear(); selected.add(it.id); selEdge = null; selChanged();
  };
  img.src = url;
}
function imageUrlFrom(dt) {
  const html = dt.getData('text/html');
  if (html) { const m = html.match(/<img[^>]+src\s*=\s*["']([^"']+)["']/i); if (m && /^https?:/i.test(m[1])) return m[1].replace(/&amp;/g, '&'); }
  const uri = (dt.getData('text/uri-list') || '').split(/\r?\n/).find(l => l && !l.startsWith('#'));
  const txt = (dt.getData('text/plain') || '').trim();
  const cand = uri || txt;
  return /^https?:\/\/\S+$/i.test(cand) || /^data:image\//i.test(cand) ? cand : null;
}
// ---- Копирование блоков: Ctrl+C / Ctrl+X / Ctrl+V ----
const CLIP_MIME = 'application/x-razvilka';
let clipMem = null, clipText = '', pasteShift = 0;
function clipFromSelection() {
  const list = selItems(); if (!list.length) return null;
  const ids = new Set(list.map(i => i.id));
  return { items: list.map(clean), edges: [...edges.values()].filter(e => ids.has(e.from) && ids.has(e.to)).map(e => ({ ...e })) };
}
const clipReadable = c => c.items.map(i => [i.title, i.text, i.label].filter(Boolean).join('\n')).filter(Boolean).join('\n\n') || 'Развилка: блоки';
function onCopy(e, cut) {
  if (editing || isTyping() || !selected.size) return;
  const c = clipFromSelection(); if (!c) return;
  e.preventDefault();
  const json = JSON.stringify(c);
  clipMem = c; clipText = clipReadable(c); pasteShift = 0;
  try { e.clipboardData.setData('text/plain', clipText); e.clipboardData.setData(CLIP_MIME, json); } catch {}
  try { localStorage.setItem('razvilka.clip', JSON.stringify({ text: clipText, data: c })); } catch {}
  if (cut) deleteSelection();
  toast((cut ? 'Вырезано' : 'Скопировано') + ': ' + c.items.length + ' ' + plural(c.items.length, 'блок', 'блока', 'блоков'), 1500);
}
const plural = (n, a, b, c) => n % 10 === 1 && n % 100 !== 11 ? a : n % 10 >= 2 && n % 10 <= 4 && (n % 100 < 10 || n % 100 >= 20) ? b : c;
document.addEventListener('copy', e => onCopy(e, false));
document.addEventListener('cut', e => onCopy(e, true));
function pasteBlocks(c) {
  if (!c || !Array.isArray(c.items) || !c.items.length) return false;
  commit();
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const o of c.items) { x0 = Math.min(x0, o.x); y0 = Math.min(y0, o.y); x1 = Math.max(x1, o.x + (o.w || 0)); y1 = Math.max(y1, o.y + (o.h || 0)); }
  const t = viewCenterWorld(); pasteShift += 24;
  const dx = Math.round(t.x - (x0 + x1) / 2 + (lastPointer ? 0 : pasteShift)), dy = Math.round(t.y - (y0 + y1) / 2 + (lastPointer ? 0 : pasteShift));
  const map = new Map(); selected.clear(); selEdge = null;
  for (const o of c.items) {
    if (!defaults(o.type)) continue;
    const copy = { ...o }; delete copy.id; delete copy.z; delete copy.x; delete copy.y;
    const n = addItem(o.type, o.x + dx, o.y + dy, copy); map.set(o.id, n.id); selected.add(n.id);
  }
  for (const e of c.edges || []) if (map.has(e.from) && map.has(e.to)) addEdge(map.get(e.from), map.get(e.to), e.label || '', edgeExtra(e));
  selChanged(); dirty();
  return true;
}
document.addEventListener('paste', e => {
  if (editing || isTyping()) return;
  const dt = e.clipboardData; if (!dt) return;
  // сначала — наши блоки (из этой вкладки, другого окна или другой доски)
  let c = null;
  try { const raw = dt.getData(CLIP_MIME); if (raw) c = JSON.parse(raw); } catch {}
  const plain = (dt.getData('text/plain') || '').trim();
  if (!c && plain && clipMem && plain === clipText.trim()) c = clipMem;
  if (!c && plain) { try { const st = JSON.parse(localStorage.getItem('razvilka.clip') || 'null'); if (st && plain === String(st.text).trim()) c = st.data; } catch {} }
  if (c && pasteBlocks(c)) { e.preventDefault(); return; }
  const url = imageUrlFrom(dt);
  if (url) { e.preventDefault(); addImageFromUrl(url, viewCenterWorld()); return; }
  const txt = (dt.getData('text/plain') || '').trim();
  if (txt) { e.preventDefault(); commit(); const it = addItem('text', viewCenterWorld().x - 140, viewCenterWorld().y - 15, { text: txt }); selected.clear(); selected.add(it.id); selChanged(); return; }
  if (dt.files && dt.files.length) toast('Загрузка файлов отключена — вставляйте ссылку на картинку (правой кнопкой → «Копировать адрес изображения»).', 5000);
});
viewport.addEventListener('dragover', e => { e.preventDefault(); });
viewport.addEventListener('drop', e => {
  e.preventDefault(); if (MOBILE) return;
  const url = imageUrlFrom(e.dataTransfer);
  if (url) addImageFromUrl(url, toWorld(vpPoint(e)));
  else if (e.dataTransfer.files.length) toast('Перетащите картинку прямо из браузера или вставьте её адрес.');
});

// ================= Выделение / действия =================
function selChanged() { updateUI(); schedule(); }
function deleteSelection() {
  if (selEdge) { commit(); removeEdge(selEdge); dirty(); updateUI(); return; }
  if (!selected.size) return;
  commit(); for (const id of [...selected]) removeItem(id); dirty(); updateUI();
}
function duplicateSelection() {
  if (!selected.size) return;
  commit();
  const map = new Map();
  for (const id of selected) {
    const o = items.get(id); const copy = clean(o); delete copy.id; delete copy.z; delete copy.x; delete copy.y;
    const c = addItem(o.type, o.x + 30, o.y + 30, copy); map.set(id, c.id);
  }
  for (const e of [...edges.values()]) if (map.has(e.from) && map.has(e.to)) addEdge(map.get(e.from), map.get(e.to), e.label, edgeExtra(e));
  selected.clear(); for (const v of map.values()) selected.add(v); selChanged();
}
const isTyping = () => { const a = document.activeElement; return a && (/^(INPUT|TEXTAREA|SELECT)$/.test(a.tagName) || a.isContentEditable); };

document.addEventListener('keydown', e => {
  if (editing) return;
  const typing = isTyping(), mod = e.ctrlKey || e.metaKey;
  if (e.key === 'Escape') { hideMenu(); hideSwatches(); if (typing) document.activeElement.blur(); else { selected.clear(); selEdge = null; selChanged(); } return; }
  if (typing) return;
  if (mod && e.code === 'KeyZ') { e.preventDefault(); e.shiftKey ? redo() : undo(); return; }
  if (mod && e.code === 'KeyA') { e.preventDefault(); selected.clear(); for (const id of items.keys()) selected.add(id); selChanged(); return; }
  if (mod && e.code === 'KeyF') { e.preventDefault(); openSearch(); return; }
  if (mod && e.code === 'KeyD') { e.preventDefault(); duplicateSelection(); return; }
  if (e.altKey && !mod && !MOBILE) {
    const m = { KeyC: 'center', KeyH: 'hcenter', KeyV: 'vcenter' }[e.code];
    if (m) { e.preventDefault(); doAlign(m); }
    return;
  }
  if (mod) return;
  if (e.key === 'Delete' || e.key === 'Backspace') { e.preventDefault(); deleteSelection(); return; }
  if (e.key === 'Enter' && selected.size === 1) { e.preventDefault(); startEdit([...selected][0]); return; }
  if (MOBILE) return;
  const map = { KeyC: ['card'], KeyT: ['text'], KeyN: ['note'], KeyR: ['callout', { variant: 'remark' }], KeyK: ['callout', { variant: 'check' }], KeyZ: ['zone'] };
  if (map[e.code]) { e.preventDefault(); const [t, pr] = map[e.code]; const wp = viewCenterWorld(); createAt(t, t === 'zone' ? { x: wp.x - 40, y: wp.y - 30 } : wp, pr); return; }
  if (e.code === 'KeyI') { e.preventDefault(); askImage(viewCenterWorld()); }
  if (e.code === 'KeyH') { e.preventDefault(); hideAllSpoilers(); }
});

// ================= Панель форматирования =================
const fmt = $('#fmt'), swatches = $('#swatches');
function selItems() { return [...selected].map(id => items.get(id)).filter(Boolean); }
function applyAll(fn, filter = () => true) {
  const list = selItems().filter(filter); if (!list.length) return;
  commit(); for (const it of list) { fn(it); touch(it); } dirty(); renderFmt();
}
function btn(html, title, fn, cls = '') {
  const b = document.createElement('button'); b.className = 'tb ' + cls; b.innerHTML = html; b.title = title;
  b.addEventListener('pointerdown', e => e.preventDefault()); // не сбивать фокус редактирования
  b.addEventListener('click', fn); return b;
}
function hideSwatches() { swatches.classList.add('hidden'); }
function showSwatches(colors, current, fn) {
  swatches.textContent = '';
  for (const c of colors) {
    const b = document.createElement('button'); b.style.background = c; if (c === current) b.className = 'on';
    b.addEventListener('pointerdown', e => e.preventDefault());
    b.addEventListener('click', () => { fn(c); hideSwatches(); });
    swatches.append(b);
  }
  swatches.classList.remove('hidden');
}
function renderFmt() {
  fmt.textContent = ''; hideSwatches();
  if (selEdge && edges.has(selEdge)) {
    const e = edges.get(selEdge);
    const lab = document.createElement('span'); lab.className = 'lbl'; lab.textContent = 'Условие перехода';
    const inp = document.createElement('input'); inp.value = e.label; inp.placeholder = 'напр. «провалили проверку»';
    let committed = false;
    inp.addEventListener('input', () => { if (!committed) { commit(); committed = true; } e.label = inp.value; dirty(); });
    inp.addEventListener('keydown', ev => { if (ev.key === 'Enter') inp.blur(); });
    fmt.append(lab, inp,
      btn('⇄', 'Развернуть направление', () => { commit(); [e.from, e.to] = [e.to, e.from]; rebuildAdj(); dirty(); }),
      btn('<svg viewBox="0 0 24 24"><path d="M4 7h16M10 11v6M14 11v6M6 7l1 13h10l1-13M9 7V4h6v3"/></svg>', 'Удалить', deleteSelection));
    fmt.classList.remove('hidden'); return;
  }
  const list = selItems();
  if (!list.length) { fmt.classList.add('hidden'); return; }
  const first = list[0];
  const textual = list.filter(it => TEXT_TYPES.has(it.type));
  const allType = t => list.every(it => it.type === t);

  if (allType('card') && !MOBILE) {
    const sel = document.createElement('select'); sel.title = 'Тип сцены';
    for (const k of KINDS) sel.add(new Option(k.name, k.id, false, k.id === first.kind));
    sel.addEventListener('change', () => applyAll(it => { it.kind = sel.value; }, it => it.type === 'card'));
    fmt.append(sel);
  }
  if (allType('callout')) {
    const sel = document.createElement('select'); sel.title = 'Вид ремарки';
    for (const [id, c] of Object.entries(CALLOUTS)) sel.add(new Option(c.name, id, false, id === first.variant));
    sel.addEventListener('change', () => applyAll(it => { it.variant = sel.value; }, it => it.type === 'callout'));
    fmt.append(sel);
  }
  if (textual.length) {
    const t0 = textual[0], onlyText = it => TEXT_TYPES.has(it.type);
    const fs = document.createElement('select'); fs.title = 'Шрифт';
    for (const f of FONTS) fs.add(new Option(f.name, f.id, false, f.id === t0.font));
    fs.addEventListener('change', () => applyAll(it => { it.font = fs.value; }, onlyText));
    const size = document.createElement('span'); size.className = 'size'; size.textContent = t0.size;
    fmt.append(fs,
      btn('−', 'Меньше', () => applyAll(it => { it.size = clamp(it.size - 2, 10, 96); }, onlyText)),
      size,
      btn('+', 'Больше', () => applyAll(it => { it.size = clamp(it.size + 2, 10, 96); }, onlyText)),
      btn('B', 'Жирный', () => applyAll(it => { it.bold = !t0.bold; }, onlyText), t0.bold ? 'on' : ''),
      btn('I', 'Курсив', () => applyAll(it => { it.italic = !t0.italic; }, onlyText), 'i ' + (t0.italic ? 'on' : '')),
      btn('U', 'Подчёркнутый', () => applyAll(it => { it.underline = !t0.underline; }, onlyText), 'u ' + (t0.underline ? 'on' : '')),
      btn(`<span class="dot" style="background:${t0.color || (t0.type === 'note' ? '#1d1f24' : 'var(--text)')}"></span>`, 'Цвет текста',
        () => showSwatches(TEXT_COLORS, t0.color, c => applyAll(it => { it.color = c; }, onlyText))),
      ...['left', 'center', 'right'].map(a => btn(alignIcon(a), { left: 'Влево', center: 'По центру', right: 'Вправо' }[a],
        () => applyAll(it => { it.align = a; }, onlyText), t0.align === a ? 'on' : '')),
    );
  }
  if (allType('note') && !MOBILE) fmt.append(btn(`<span class="dot" style="background:${first.bg}"></span>`, 'Цвет заметки',
    () => showSwatches(NOTE_COLORS, first.bg, c => applyAll(it => { it.bg = c; }, it => it.type === 'note'))));
  if (allType('zone')) fmt.append(btn(`<span class="dot" style="background:${first.color}"></span>`, 'Цвет зоны',
    () => showSwatches(ZONE_COLORS, first.color, c => applyAll(it => { it.color = c; }, it => it.type === 'zone'))));
  if (allType('image') && list.length === 1) fmt.append(
    btn('↗', 'Открыть оригинал', () => openExternal(first.src)),
    btn('1:1', 'Исходные пропорции', () => { const el = itemEls.get(first.id)?.querySelector('img'); if (el && el.naturalWidth) applyAll(it => { it.h = Math.round(it.w * el.naturalHeight / el.naturalWidth); }); }),
  );
  if (!MOBILE && list.some(it => it.type === 'card' && paraList(it.text).some(p => CHECK_RE.test(p))))
    fmt.append(btn('🎲', 'Вынести проверки на поля (со стрелкой в нужный абзац)', () => {
      commit(); const n = extractChecks(list.filter(it => it.type === 'card'), { measure: estH });
      if (n) { dirty(); toast('Вынесено проверок: ' + n, 2000); } else { undoStack.pop(); updateUI(); toast('Все проверки уже вынесены', 2000); }
    }));
  if (!MOBILE && alignPlan()) fmt.append(btn(ALIGN_ICON, 'Выровнять / центрировать', ev => showAlignMenu(ev.currentTarget)));
  if (TEXT_TYPES.has(first.type) || first.type === 'zone') fmt.append(btn('✎', 'Редактировать текст', () => startEdit(first.id)));
  const spoAble = list.filter(it => it.type !== 'zone');
  if (spoAble.length) {
    const allSpo = spoAble.every(it => it.spoiler);
    fmt.append(btn('<svg viewBox="0 0 24 24"><path d="M3 3l18 18"/><path d="M10.6 5.1A10 10 0 0 1 12 5c5 0 9 4.5 10 7a13 13 0 0 1-3.2 4.2M6.6 6.6A13 13 0 0 0 2 12c1 2.5 5 7 10 7a9.8 9.8 0 0 0 5.4-1.6"/><path d="M9.9 9.9a3 3 0 0 0 4.2 4.2"/></svg>',
      allSpo ? 'Убрать спойлер' : 'Спойлер — скрыть от игроков (H — скрыть все открытые)',
      () => applyAll(it => { it.spoiler = !allSpo; if (allSpo) revealed.delete(it.id); }, it => it.type !== 'zone'), allSpo ? 'on' : ''));
  }
  fmt.append(btn('<svg viewBox="0 0 24 24"><path d="M4 7h16M10 11v6M14 11v6M6 7l1 13h10l1-13M9 7V4h6v3"/></svg>', 'Удалить', deleteSelection));
  fmt.classList.remove('hidden');
}
function alignIcon(a) {
  const l = { left: 'M4 6h16M4 12h10M4 18h14', center: 'M4 6h16M7 12h10M5 18h14', right: 'M4 6h16M10 12h10M6 18h14' }[a];
  return `<svg viewBox="0 0 24 24"><path d="${l}"/></svg>`;
}
function rebuildAdj() { adj.clear(); for (const e of edges.values()) adjAdd(e); }

// ================= Проверки на полях: стрелка-указатель в абзац сцены =================
// Абзацы текста карточки — куски, разделённые пустой строкой.
function paraStarts(text) {
  const res = [], re = /\n{2,}/g; let pos = 0, m;
  text = String(text || '');
  while ((m = re.exec(text))) { if (text.slice(pos, m.index).trim()) res.push(pos); pos = m.index + m[0].length; }
  if (text.slice(pos).trim()) res.push(pos);
  return res;
}
const paraList = text => String(text || '').split(/\n{2,}/).filter(p => p.trim());
// Вертикальная середина первой строки каждого абзаца — в координатах карточки.
function paraYFromEl(el, it, scale) {
  const f = el.querySelector('.ctext'); const node = f && f.firstChild;
  if (!node || node.nodeType !== 3 || !f.offsetHeight) return null;
  const base = el.getBoundingClientRect().top, len = node.length;
  return paraStarts(it.text).map(st => {
    if (st >= len) return null;
    const r = document.createRange(); r.setStart(node, st); r.setEnd(node, Math.min(st + 1, len));
    const rc = r.getClientRects()[0] || r.getBoundingClientRect();
    return rc ? (rc.top - base + rc.height / 2) / scale : null;
  });
}
function anchorIndex(card, e) {
  const ps = paraList(card.text);
  if (e.anchorText) { const k = ps.findIndex(p => p.trim().startsWith(e.anchorText)); if (k >= 0) return k; }
  return Math.max(0, Math.min(ps.length - 1, e.anchor | 0));
}
function pinGeo(a, b, e) {
  const k = anchorIndex(b, e), py = b._paraY && b._paraY[k] != null ? b.y + b._paraY[k] : b.y + Math.min(b.h / 2, 40);
  const acx = a.x + a.w / 2, left = acx < b.x + b.w / 2;
  const p2x = left ? b.x : b.x + b.w, p1x = left ? a.x + a.w : a.x, p1y = a.y + Math.min(a.h / 2, 26);
  const dx = Math.max(30, Math.abs(p2x - p1x) / 2) * (left ? 1 : -1);
  return { d: `M${r1(p1x)},${r1(p1y)} C${r1(p1x + dx)},${r1(p1y)} ${r1(p2x - dx)},${r1(py)} ${r1(p2x)},${r1(py)}`, mx: 0, my: 0 };
}
// Абзац под курсором при отпускании стрелки на карточке.
function paraAtPoint(card, clientX, clientY) {
  let node = null, off = 0;
  if (document.caretRangeFromPoint) { const r = document.caretRangeFromPoint(clientX, clientY); if (r) { node = r.startContainer; off = r.startOffset; } }
  else if (document.caretPositionFromPoint) { const p = document.caretPositionFromPoint(clientX, clientY); if (p) { node = p.offsetNode; off = p.offset; } }
  const el = itemEls.get(card.id), f = el && el.querySelector('.ctext');
  if (!node || !f || !f.contains(node)) return null;
  const starts = paraStarts(card.text); let k = 0;
  for (let i = 0; i < starts.length; i++) if (off >= starts[i]) k = i;
  return k;
}
const CHECK_RE = /^\s*(🎲|⚡|Проверка:|Спасбросок)/;
// Вынести абзацы-проверки сцены на поля: блок слева на уровне абзаца + стрелка в этот абзац.
function extractChecks(cards, opt = {}) {
  const W = opt.width || 250, GAP = opt.gap || 70; let made = 0;
  for (const c of cards) {
    if (c.type !== 'card') continue;
    const ps = paraList(c.text);
    const have = new Set([...(adj.get(c.id) || [])].map(id => edges.get(id)).filter(e => e && e.kind === 'pin' && e.to === c.id).map(e => e.anchorText));
    let py = opt.paraY ? opt.paraY(c) : (c._paraY || null), bottom = -Infinity;
    ps.forEach((p, k) => {
      if (!CHECK_RE.test(p)) return;
      const anchorText = p.trim().slice(0, 40);
      if (have.has(anchorText)) return;
      const yWant = c.y + (py && py[k] != null ? py[k] : 30 + k * 40) - 22;
      const it = addItem('callout', c.x - W - GAP, Math.max(yWant, bottom + 12), { variant: 'check', w: W, text: p.trim().replace(/^Проверка:\s*/, '🎲 ') });
      it.h = opt.measure ? opt.measure(it) : 60; bottom = it.y + it.h;
      const e = addEdge(it.id, c.id, ''); if (e) { e.kind = 'pin'; e.anchor = k; e.anchorText = anchorText; }
      made++;
    });
  }
  return made;
}

// ================= Выравнивание =================
const ALIGN_ICON = '<svg viewBox="0 0 24 24"><rect x="4" y="4" width="16" height="16" rx="2"/><path d="M12 8v8M8 12h8"/></svg>';
const contains = (c, o) => o.x >= c.x && o.y >= c.y && o.x + o.w <= c.x + c.w && o.y + o.h <= c.y + c.h;
const area = o => o.w * o.h;
function refName(r) {
  if (!r.id) return 'выделения';
  if (r.type === 'zone') return `зоны «${r.label || 'без названия'}»`;
  if (r.type === 'card') return `сцены «${r.title || 'без названия'}»`;
  return { text: 'текста', note: 'заметки', callout: 'ремарки', image: 'картинки' }[r.type] || 'блока';
}
// Что двигаем и относительно чего:
//  • один блок — внутри самой маленькой зоны/блока, в котором он целиком лежит;
//  • несколько, и один из них вмещает остальные — относительно него (группа двигается целиком);
//  • иначе — относительно общих границ выделения (каждый блок по отдельности).
function alignPlan() {
  const list = selItems(); if (!list.length) return null;
  if (list.length === 1) {
    const it = list[0];
    let ref = null;
    for (const c of items.values()) if (c !== it && contains(c, it) && (!ref || area(c) < area(ref))) ref = c;
    return ref ? { ref, movers: [it], group: true, pad: 16 } : null;
  }
  const cont = list.filter(c => list.every(o => o === c || contains(c, o))).sort((a, b) => area(a) - area(b))[0];
  if (cont) return { ref: cont, movers: list.filter(o => o !== cont), group: true, pad: 16 };
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  for (const o of list) { x0 = Math.min(x0, o.x); y0 = Math.min(y0, o.y); x1 = Math.max(x1, o.x + o.w); y1 = Math.max(y1, o.y + o.h); }
  return { ref: { x: x0, y: y0, w: x1 - x0, h: y1 - y0 }, movers: list, group: false, pad: 0 };
}
function doAlign(mode) {
  const plan = alignPlan(); if (!plan) return;
  const { ref, movers, group, pad } = plan;
  commit();
  // зона при сдвиге тащит своё содержимое, как и при перетаскивании
  const moveBy = (o, dx, dy) => {
    if (o.type === 'zone') for (const c of items.values()) if (c !== o && !movers.includes(c) && contains(o, c)) { c.x = Math.round(c.x + dx); c.y = Math.round(c.y + dy); }
    o.x = Math.round(o.x + dx); o.y = Math.round(o.y + dy);
  };
  const target = (b, m) => {
    let dx = 0, dy = 0;
    if (m === 'left') dx = ref.x + pad - b.x;
    if (m === 'hcenter' || m === 'center') dx = ref.x + (ref.w - b.w) / 2 - b.x;
    if (m === 'right') dx = ref.x + ref.w - pad - (b.x + b.w);
    if (m === 'top') dy = ref.y + pad - b.y;
    if (m === 'vcenter' || m === 'center') dy = ref.y + (ref.h - b.h) / 2 - b.y;
    if (m === 'bottom') dy = ref.y + ref.h - pad - (b.y + b.h);
    return [dx, dy];
  };
  if (mode === 'dist-h' || mode === 'dist-v') {
    const hz = mode === 'dist-h', ms = [...movers].sort((a, b) => hz ? a.x - b.x : a.y - b.y);
    const total = ms.reduce((s, o) => s + (hz ? o.w : o.h), 0);
    const gap = ((hz ? ref.w : ref.h) - 2 * pad - total) / (ms.length - 1);
    let pos = (hz ? ref.x : ref.y) + pad;
    for (const o of ms) { moveBy(o, hz ? pos - o.x : 0, hz ? 0 : pos - o.y); pos += (hz ? o.w : o.h) + gap; }
  } else if (group) {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (const o of movers) { x0 = Math.min(x0, o.x); y0 = Math.min(y0, o.y); x1 = Math.max(x1, o.x + o.w); y1 = Math.max(y1, o.y + o.h); }
    const [dx, dy] = target({ x: x0, y: y0, w: x1 - x0, h: y1 - y0 }, mode);
    for (const o of movers) moveBy(o, dx, dy);
  } else for (const o of movers) { const [dx, dy] = target(o, mode); moveBy(o, dx, dy); }
  dirty();
}
function showAlignMenu(b) {
  const plan = alignPlan(); if (!plan) return;
  const r = b.getBoundingClientRect();
  const opts = [
    ['center', 'Центрировать', 'Alt+C'], ['hcenter', 'По центру по горизонтали', 'Alt+H'], ['vcenter', 'По центру по вертикали', 'Alt+V'],
    ['left', 'По левому краю', ''], ['right', 'По правому краю', ''], ['top', 'По верхнему краю', ''], ['bottom', 'По нижнему краю', ''],
  ];
  const entries = opts.map(([m, label, key]) => ({ label, key, fn: () => doAlign(m) }));
  if (plan.movers.length >= 3) entries.push({ label: 'Распределить по горизонтали', fn: () => doAlign('dist-h') }, { label: 'Распределить по вертикали', fn: () => doAlign('dist-v') });
  showMenu(r.left, 0, entries, 'Относительно ' + refName(plan.ref));
  const m = $('#menu'); m.style.top = Math.max(8, r.top - m.offsetHeight - 8) + 'px';
}

// ================= Тема =================
function setTheme(t) {
  document.documentElement.dataset.theme = t;
  $('meta[name="theme-color"]').content = t === 'light' ? '#f3f1ec' : '#14161b';
  try { localStorage.setItem('razvilka.theme', t); } catch {}
}
function toggleTheme() { setTheme(document.documentElement.dataset.theme === 'light' ? 'dark' : 'light'); }
{ let t = 'dark'; try { t = localStorage.getItem('razvilka.theme') || 'dark'; } catch {} setTheme(t); }

// ================= Акцентный цвет =================
const ACCENTS = [
  ['Золото (по умолчанию)', ''], ['Оранжевый', '#f08a3c'], ['Красный', '#e5484d'], ['Розовый', '#ec6fb4'],
  ['Фиолетовый', '#9b7bf5'], ['Синий', '#4f8ff7'], ['Бирюзовый', '#2fb5a8'], ['Зелёный', '#5fbf5a'],
];
function setAccent(c) {
  const root = document.documentElement.style;
  if (!c) { root.removeProperty('--accent'); root.removeProperty('--on-accent'); }
  else {
    root.setProperty('--accent', c);
    // текст на акцентных кнопках — тёмный на светлых цветах, белый на тёмных
    const n = parseInt(c.slice(1), 16), r = n >> 16 & 255, g = n >> 8 & 255, b = n & 255;
    const lum = (0.299 * r + 0.587 * g + 0.114 * b) / 255;
    root.setProperty('--on-accent', lum > 0.6 ? '#111' : '#fff');
  }
  try { c ? localStorage.setItem('razvilka.accent', c) : localStorage.removeItem('razvilka.accent'); } catch {}
}
{ let a = ''; try { a = localStorage.getItem('razvilka.accent') || ''; } catch {} if (/^#[0-9a-f]{6}$/i.test(a)) setAccent(a); }
function accentMenu(btnEl) {
  const r = btnEl.getBoundingClientRect();
  let cur = ''; try { cur = localStorage.getItem('razvilka.accent') || ''; } catch {}
  const entries = ACCENTS.map(([label, c]) => ({ label: (c === cur ? '✓ ' : '') + label, mk: c || '#f0c060', fn: () => setAccent(c) }));
  entries.push({ label: 'Свой цвет…', mk: 'conic-gradient(red, yellow, lime, cyan, blue, magenta, red)', fn: () => colorPicker(btnEl, cur || '#f0c060') });
  showMenu(r.left, r.bottom + 6, entries, 'Акцентный цвет');
  for (const m of menu.querySelectorAll('.mk')) { m.classList.add('round'); if (m.style.background.startsWith('conic')) m.style.background = 'conic-gradient(red, yellow, lime, cyan, blue, magenta, red)'; }
}
// Своя палитра: ползунки оттенка, насыщенности и яркости + код цвета. Работает и на телефоне.
const hsl2hex = (h, s, l) => {
  s /= 100; l /= 100; const k = n => (n + h / 30) % 12, a = s * Math.min(l, 1 - l);
  const f = n => Math.round(255 * (l - a * Math.max(-1, Math.min(k(n) - 3, 9 - k(n), 1)))).toString(16).padStart(2, '0');
  return '#' + f(0) + f(8) + f(4);
};
function hex2hsl(hex) {
  const n = parseInt(hex.slice(1), 16); let r = (n >> 16 & 255) / 255, g = (n >> 8 & 255) / 255, b = (n & 255) / 255;
  const mx = Math.max(r, g, b), mn = Math.min(r, g, b), l = (mx + mn) / 2; let h = 0, s = 0;
  if (mx !== mn) { const d = mx - mn; s = l > .5 ? d / (2 - mx - mn) : d / (mx + mn);
    h = mx === r ? (g - b) / d + (g < b ? 6 : 0) : mx === g ? (b - r) / d + 2 : (r - g) / d + 4; h *= 60; }
  return [Math.round(h), Math.round(s * 100), Math.round(l * 100)];
}
function colorPicker(anchorEl, start) {
  if (popClose) popClose(null);
  const before = (() => { try { return localStorage.getItem('razvilka.accent') || ''; } catch { return ''; } })();
  let [h, sat, lig] = hex2hsl(start);
  const pop = document.createElement('div'); pop.className = 'pop from-top cpick';
  pop.innerHTML = `<div class="pop-title">Свой цвет</div>
    <div class="cp-prev"><span class="cp-sw"></span><input class="pop-input cp-hex" maxlength="7" spellcheck="false"></div>
    <label class="pop-lab">Оттенок<input type="range" class="cp-r cp-h" min="0" max="360"></label>
    <label class="pop-lab">Насыщенность<input type="range" class="cp-r cp-s" min="20" max="100"></label>
    <label class="pop-lab">Яркость<input type="range" class="cp-r cp-l" min="30" max="75"></label>
    <div class="pop-btns"><button class="btn ghost cp-cancel">Отмена</button><button class="btn primary cp-ok">Готово</button></div><div class="pop-arrow"></div>`;
  document.body.append(pop);
  const $p = q => pop.querySelector(q), hexIn = $p('.cp-hex'), rh = $p('.cp-h'), rs = $p('.cp-s'), rl = $p('.cp-l');
  const paint = (fromHex) => {
    const hex = hsl2hex(h, sat, lig);
    $p('.cp-sw').style.background = hex; if (!fromHex) hexIn.value = hex;
    rh.value = h; rs.value = sat; rl.value = lig;
    rs.style.background = `linear-gradient(90deg, ${hsl2hex(h, 20, lig)}, ${hsl2hex(h, 100, lig)})`;
    rl.style.background = `linear-gradient(90deg, ${hsl2hex(h, sat, 30)}, ${hsl2hex(h, sat, 75)})`;
    setAccent(hex);
  };
  rh.oninput = () => { h = +rh.value; paint(); }; rs.oninput = () => { sat = +rs.value; paint(); }; rl.oninput = () => { lig = +rl.value; paint(); };
  hexIn.oninput = () => { const v = hexIn.value.trim(); if (/^#?[0-9a-f]{6}$/i.test(v)) { [h, sat, lig] = hex2hsl(v[0] === '#' ? v : '#' + v); paint(true); } };
  paint();
  const r = anchorEl.getBoundingClientRect(), pw = pop.offsetWidth;
  const x = clamp(r.left + r.width / 2 - pw / 2, 8, innerWidth - pw - 8);
  pop.style.left = x + 'px'; pop.style.top = (r.bottom + 12) + 'px';
  $p('.pop-arrow').style.left = clamp(r.left + r.width / 2 - x - 7, 12, pw - 26) + 'px';
  requestAnimationFrame(() => pop.classList.add('show'));
  const close = keep => { if (!pop.isConnected) return; pop.remove(); document.removeEventListener('pointerdown', outside, true); popClose = null; if (!keep) setAccent(before); };
  const outside = e => { if (!pop.contains(e.target)) close(true); };
  setTimeout(() => document.addEventListener('pointerdown', outside, true), 0);
  $p('.cp-ok').onclick = () => close(true); $p('.cp-cancel').onclick = () => close(false);
  pop.addEventListener('keydown', e => { if (e.key === 'Escape') { e.stopPropagation(); close(false); } if (e.key === 'Enter') close(true); });
  popClose = () => close(true);
}

// ================= Справка =================
function toggleHelp(force) {
  const h = $('#help'), show = force !== undefined ? force : h.classList.contains('hidden');
  h.classList.toggle('hidden', !show); $('#helpBtn').classList.toggle('on', show);
}
if (MOBILE) $('#helpDesk').remove(); else $('#helpMob').remove();

// ================= Общее обновление интерфейса =================

function updateUI() {
  $('[data-act="undo"]').disabled = !undoStack.length;
  $('[data-act="redo"]').disabled = !redoStack.length;
  $('[data-act="boxmode"]').classList.toggle('on', boxMode);
  renderFmt();
}

// ================= Меню =================
const menu = $('#menu');
function showMenu(x, y, entries, title) {
  menu.textContent = '';
  if (title) { const t = document.createElement('div'); t.className = 'mtitle'; t.textContent = title; menu.append(t); }
  for (const en of entries) {
    const b = document.createElement('button');
    if (en.danger) b.className = 'danger';
    if (en.mk) { const m = document.createElement('span'); m.className = 'mk'; m.style.background = en.mk; b.append(m); }
    const s = document.createElement('span'); s.textContent = en.label; b.append(s);
    if (en.key) { const k = document.createElement('span'); k.className = 'key'; k.textContent = en.key; b.append(k); }
    b.addEventListener('click', () => { hideMenu(); en.fn(); });
    menu.append(b);
  }
  menu.classList.remove('hidden');
  const r = menu.getBoundingClientRect();
  menu.style.left = clamp(x, 8, innerWidth - r.width - 8) + 'px';
  menu.style.top = clamp(y, 8, innerHeight - r.height - 8) + 'px';
}
function hideMenu() { menu.classList.add('hidden'); }
document.addEventListener('pointerdown', e => {
  if (!menu.contains(e.target) && !e.target.closest('.more') && !e.target.closest('[data-act="insert"]') && !e.target.closest('[data-act="accent"]')) hideMenu();
  if (!swatches.contains(e.target) && !fmt.contains(e.target)) hideSwatches();
}, true);

// ================= Поиск =================
function openSearch() { $('#searchBox').classList.remove('hidden'); $('#searchInput').focus(); $('#searchInput').select(); }
function closeSearch() { $('#searchBox').classList.add('hidden'); $('#searchInput').value = ''; runSearch(''); }
function runSearch(q) {
  q = q.trim().toLowerCase(); searchSet = new Set(); searchHits = []; searchIdx = -1;
  if (q) for (const it of items.values()) {
    const t = [it.title, it.text, it.label].filter(Boolean).join('\n').toLowerCase();
    if (t.includes(q)) { searchSet.add(it.id); searchHits.push(it.id); }
  }
  $('#searchCount').textContent = q ? String(searchHits.length) : '';
  schedule();
}
function nextHit() {
  if (!searchHits.length) return;
  searchIdx = (searchIdx + 1) % searchHits.length;
  const it = items.get(searchHits[searchIdx]); if (!it) return;
  selected.clear(); selected.add(it.id); selEdge = null; selChanged(); centerOn(it);
}
$('#searchInput').addEventListener('input', e => runSearch(e.target.value));
$('#searchInput').addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); nextHit(); } if (e.key === 'Escape') closeSearch(); });

// ================= Папки и доски =================
const tree = $('#tree'), sidebar = $('#sidebar');
function boardPath(b) {
  const parts = []; let f = b && ws.folders.find(x => x.id === b.folder);
  while (f) { parts.unshift(f.name); f = ws.folders.find(x => x.id === f.parent); }
  return parts;
}
function renderCrumb() {
  const b = ws.boards.find(b => b.id === boardId); const c = $('#crumb'); c.textContent = '';
  const path = boardPath(b);
  if (path.length) { const m = document.createElement('span'); m.className = 'muted'; m.textContent = path.join(' / ') + ' / '; c.append(m); }
  c.append(document.createTextNode(b ? b.name : '—'));
  document.title = (b ? b.name + ' — ' : '') + 'Развилка';
}
function renderTree() {
  tree.textContent = '';
  const walk = (parent, depth) => {
    const folders = ws.folders.filter(f => (f.parent || null) === parent).sort((a, b) => a.name.localeCompare(b.name, 'ru'));
    for (const f of folders) {
      tree.append(row(depth, f.open ? '▾' : '▸', f.name, false, () => { f.open = !f.open; saveWs(); renderTree(); }, ev => folderMenu(f, ev)));
      if (f.open) walk(f.id, depth + 1);
    }
    const boards = ws.boards.filter(b => (b.folder || null) === parent).sort((a, b) => a.name.localeCompare(b.name, 'ru'));
    for (const b of boards) tree.append(row(depth, '▤', b.name, b.id === boardId, () => { openBoard(b.id); if (MOBILE) toggleSidebar(false); }, ev => boardMenu(b, ev)));
  };
  walk(null, 0);
}
function row(depth, icon, name, cur, onClick, onMore) {
  const r = document.createElement('div'); r.className = 'row' + (cur ? ' cur' : ''); r.style.setProperty('--d', depth);
  r.innerHTML = '<span class="ic"></span><span class="nm"></span><button class="more" title="Действия">⋯</button>';
  r.children[0].textContent = icon; r.children[1].textContent = name;
  r.addEventListener('click', e => { if (!e.target.closest('.more')) onClick(); });
  r.querySelector('.more').addEventListener('click', e => { e.stopPropagation(); onMore(e); });
  return r;
}
// ================= Своё окошко рядом с кнопкой (вместо браузерных prompt/confirm) =================
let popClose = null;
function anchorRect(a) { if (!a) return null; if (a.getBoundingClientRect) return a.getBoundingClientRect(); return a; }
// opt: { anchor, title, message, value, placeholder, ok, danger, where: { value, exclude }, input: false }
function popAsk(opt) {
  if (popClose) popClose(null);
  return new Promise(resolve => {
    const pop = document.createElement('div'); pop.className = 'pop';
    const head = document.createElement('div'); head.className = 'pop-title'; head.textContent = opt.title || ''; pop.append(head);
    if (opt.message) { const m = document.createElement('div'); m.className = 'pop-msg'; m.textContent = opt.message; pop.append(m); }
    let inp = null, sel = null;
    if (opt.input !== false) {
      inp = document.createElement('input'); inp.className = 'pop-input'; inp.value = opt.value || ''; inp.placeholder = opt.placeholder || '';
      inp.spellcheck = false; pop.append(inp);
    }
    if (opt.where) {
      const lab = document.createElement('label'); lab.className = 'pop-lab'; lab.textContent = 'Где создать';
      sel = document.createElement('select'); sel.className = 'pop-input';
      sel.add(new Option('⌂ Корень (без папки)', ''));
      for (const f of [...ws.folders].sort((a, b) => boardPath({ folder: a.id }).join('/').localeCompare(boardPath({ folder: b.id }).join('/'), 'ru'))) {
        if (opt.where.exclude && isInside(f.id, opt.where.exclude)) continue;
        sel.add(new Option('📁 ' + boardPath({ folder: f.id }).join(' / '), f.id, false, f.id === opt.where.value));
      }
      lab.append(sel); pop.append(lab);
    }
    const row = document.createElement('div'); row.className = 'pop-btns';
    const cancel = document.createElement('button'); cancel.className = 'btn ghost'; cancel.textContent = 'Отмена';
    const ok = document.createElement('button'); ok.className = 'btn ' + (opt.danger ? 'danger' : 'primary'); ok.textContent = opt.ok || 'Готово';
    row.append(cancel, ok); pop.append(row);
    const arrow = document.createElement('div'); arrow.className = 'pop-arrow'; pop.append(arrow);
    document.body.append(pop);
    // позиция: справа от того, откуда вызвали; если не влезает — снизу
    const r = anchorRect(opt.anchor) || { left: innerWidth / 2 - 150, right: innerWidth / 2 - 150, top: 120, bottom: 120, height: 0, width: 0 };
    const pw = pop.offsetWidth, ph = pop.offsetHeight;
    let x = r.right + 14, y = r.top + r.height / 2 - 28, side = 'left';
    if (x + pw > innerWidth - 8) { x = Math.max(8, Math.min(r.left, innerWidth - pw - 8)); y = r.bottom + 12; side = 'top'; }
    y = clamp(y, 8, innerHeight - ph - 8);
    pop.style.left = x + 'px'; pop.style.top = y + 'px'; pop.classList.add('from-' + side);
    if (side === 'left') arrow.style.top = clamp(r.top + r.height / 2 - y - 7, 12, ph - 26) + 'px';
    else arrow.style.left = clamp(r.left + r.width / 2 - x - 7, 12, pw - 26) + 'px';
    requestAnimationFrame(() => pop.classList.add('show'));
    const done = v => {
      if (!pop.isConnected) return;
      pop.remove(); document.removeEventListener('pointerdown', outside, true); popClose = null; resolve(v);
    };
    const submit = () => {
      const v = inp ? inp.value.trim() : true;
      if (inp && !v) { inp.classList.add('bad'); inp.focus(); return; }
      done({ value: v, folder: sel ? (sel.value || null) : undefined });
    };
    const outside = e => { if (!pop.contains(e.target)) done(null); };
    setTimeout(() => document.addEventListener('pointerdown', outside, true), 0);
    pop.addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); submit(); } if (e.key === 'Escape') { e.preventDefault(); e.stopPropagation(); done(null); } });
    ok.addEventListener('click', submit); cancel.addEventListener('click', () => done(null));
    popClose = done;
    setTimeout(() => { if (inp) { inp.focus(); inp.select(); } else ok.focus(); }, 30);
  });
}
// окошко от кнопок боковой панели — сразу за её правым краем, на уровне кнопки
const sideAnchor = el => { const r = el.getBoundingClientRect(), sb = sidebar.getBoundingClientRect(); return { left: r.left, right: Math.max(r.right, sb.right - 4), top: r.top, bottom: r.bottom, width: r.width, height: r.height }; };
const rowOf = ev => { const el = ev && ev.target && ev.target.closest ? (ev.target.closest('.row') || ev.target) : null; return el && sidebar.contains(el) ? sideAnchor(el) : el; };

function folderMenu(f, ev) {
  const at = rowOf(ev);
  showMenu(ev.clientX, ev.clientY, [
    { label: 'Новая доска здесь', fn: () => newBoard(f.id, undefined, at) },
    { label: 'Новая папка внутри', fn: () => newFolder(f.id, at) },
    { label: 'Переименовать', fn: async () => { const r = await popAsk({ anchor: at, title: 'Переименовать папку', value: f.name, ok: 'Сохранить' }); if (r) { f.name = r.value; saveWs(); renderTree(); renderCrumb(); } } },
    { label: 'Переместить в…', fn: () => moveMenu(ev, f.id, p => { f.parent = p; }) },
    { label: 'Удалить папку', danger: true, fn: () => deleteFolder(f, at) },
  ]);
}
function boardMenu(b, ev) {
  const at = rowOf(ev);
  showMenu(ev.clientX, ev.clientY, [
    { label: 'Переименовать', fn: async () => { const r = await popAsk({ anchor: at, title: 'Переименовать доску', value: b.name, ok: 'Сохранить' }); if (r) { b.name = r.value; saveWs(); renderTree(); renderCrumb(); } } },
    { label: 'Переместить в…', fn: () => moveMenu(ev, null, p => { b.folder = p; }) },
    { label: 'Дублировать', fn: () => duplicateBoard(b) },
    { label: 'Экспорт доски (.json)', fn: () => exportBoard(b) },
    { label: 'Экспорт в Word (.docx)', fn: async () => { if (b.id !== boardId) await openBoard(b.id); exportDocx(); } },
    { label: 'Удалить доску', danger: true, fn: () => deleteBoard(b, at) },
  ]);
}
function isInside(folderId, maybeParent) { let f = ws.folders.find(x => x.id === folderId); while (f) { if (f.id === maybeParent) return true; f = ws.folders.find(x => x.id === f.parent); } return false; }
function moveMenu(ev, selfFolder, apply) {
  const opts = [{ label: '⌂ Корень', fn: () => { apply(null); saveWs(); renderTree(); renderCrumb(); } }];
  for (const f of ws.folders) {
    if (selfFolder && isInside(f.id, selfFolder)) continue;
    opts.push({ label: '📁 ' + boardPath({ folder: f.id }).join(' / '), fn: () => { apply(f.id); f.open = true; saveWs(); renderTree(); renderCrumb(); } });
  }
  setTimeout(() => showMenu(ev.clientX, ev.clientY, opts, 'Куда переместить'), 0);
}
async function newFolder(parent = null, anchor) {
  const r = await popAsk({ anchor, title: 'Новая папка', value: 'Новая папка', placeholder: 'Например: Партия 2', ok: 'Создать', where: { value: parent } });
  if (!r) return; parent = r.folder;
  ws.folders.push({ id: uid(), name: r.value, parent, open: true });
  if (parent) { const p = ws.folders.find(f => f.id === parent); if (p) p.open = true; }
  saveWs(); renderTree();
}
async function newBoard(folder = undefined, name, anchor) {
  if (folder === undefined) { const cur = ws.boards.find(b => b.id === boardId); folder = cur ? cur.folder : null; }
  if (!name) {
    const r = await popAsk({ anchor, title: 'Новая доска', value: 'Новая доска', placeholder: 'Например: Сценарий, Карта связей', ok: 'Создать', where: { value: folder } });
    if (!r) return; name = r.value; folder = r.folder;
  }
  if (!name || !name.trim()) return;
  const id = uid();
  ws.boards.push({ id, name: name.trim(), folder, updated: Date.now() });
  await DB.put('boards', { id, items: [], edges: [], view: null });
  await saveWs(); await openBoard(id);
}
async function duplicateBoard(b) {
  if (b.id === boardId) await saveNow();
  const d = await DB.get('boards', b.id); if (!d) return;
  const id = uid();
  ws.boards.push({ id, name: b.name + ' (копия)', folder: b.folder, updated: Date.now() });
  await DB.put('boards', { ...d, id }); await saveWs(); renderTree();
}
async function deleteBoard(b, anchor) {
  if (!await popAsk({ anchor, title: 'Удалить доску?', message: `«${b.name}» удалится вместе со всем содержимым. Отменить это будет нельзя.`, input: false, ok: 'Удалить', danger: true })) return;
  ws.boards = ws.boards.filter(x => x.id !== b.id); await DB.del('boards', b.id);
  if (b.id === boardId) {
    boardId = null;
    if (ws.boards.length) await openBoard(ws.boards[0].id); else await newBoard(null, 'Новая доска');
  }
  await saveWs(); renderTree();
}
async function deleteFolder(f, anchor) {
  const ids = new Set([f.id]); let grew = true;
  while (grew) { grew = false; for (const x of ws.folders) if (x.parent && ids.has(x.parent) && !ids.has(x.id)) { ids.add(x.id); grew = true; } }
  const boards = ws.boards.filter(b => ids.has(b.folder));
  if (!await popAsk({ anchor, title: 'Удалить папку?', message: boards.length ? `«${f.name}» удалится вместе с досками внутри (${boards.length}). Отменить это будет нельзя.` : `Папка «${f.name}» пустая.`, input: false, ok: 'Удалить', danger: true })) return;
  for (const b of boards) await DB.del('boards', b.id);
  ws.boards = ws.boards.filter(b => !ids.has(b.folder)); ws.folders = ws.folders.filter(x => !ids.has(x.id));
  if (!ws.boards.find(b => b.id === boardId)) { boardId = null; if (ws.boards.length) await openBoard(ws.boards[0].id); else await newBoard(null, 'Новая доска'); }
  await saveWs(); renderTree();
}
async function openBoard(id) {
  stopEdit();
  if (boardId && boardId !== id) await saveNow();
  const d = await DB.get('boards', id);
  boardId = id; ws.current = id; saveWs();
  loadData(d ? d.items : [], d ? d.edges : []);
  undoStack.length = 0; redoStack.length = 0;
  selected.clear(); selEdge = null; closeSearch();
  if (d && d.view) Object.assign(view, d.view); else { schedule(); requestAnimationFrame(() => requestAnimationFrame(fit)); }
  renderCrumb(); renderTree(); updateUI(); schedule();
}
function toggleSidebar(force) {
  const show = force !== undefined ? force : sidebar.classList.contains('hidden');
  sidebar.classList.toggle('hidden', !show);
  if (show) renderTree();
}

// ================= Экспорт / импорт =================
function download(name, obj) {
  return saveBlob(name, new Blob([JSON.stringify(obj)], { type: 'application/json' }), 'json', 'Развилка (JSON)');
}
async function exportBoard(b) {
  if (b.id === boardId) await saveNow();
  const d = await DB.get('boards', b.id);
  download(b.name, { app: 'razvilka', kind: 'board', version: 1, name: b.name, items: d?.items || [], edges: d?.edges || [] });
}
async function exportAll() {
  await saveNow();
  const boards = await DB.all('boards');
  download('Развилка — вся кампания ' + new Date().toISOString().slice(0, 10), { app: 'razvilka', kind: 'workspace', version: 1, ws, boards });
}
$('#importFile').addEventListener('change', async e => {
  const file = e.target.files[0]; e.target.value = ''; if (!file) return;
  let d; try { d = parseLoose(await file.text()); } catch { importMode = 'add'; toast('Файл не читается как JSON'); return; }
  if (importMode === 'restore') {
    importMode = 'add';
    if (d.kind === 'workspace' && d.ws && Array.isArray(d.boards)) return restoreWorkspace(d);
    toast('Это не резервная копия всей кампании (нужен файл «Развилка — кампания.json» или «бэкап»)', 6000); return;
  }
  try {
    if (d.kind === 'workspace' && d.ws && Array.isArray(d.boards)) {
      // добавляем как отдельную папку, ничего не затирая
      const root = { id: uid(), name: 'Импорт ' + new Date().toLocaleDateString('ru'), parent: null, open: true };
      const fmap = new Map(); for (const f of d.ws.folders || []) fmap.set(f.id, uid());
      ws.folders.push(root);
      for (const f of d.ws.folders || []) ws.folders.push({ ...f, id: fmap.get(f.id), parent: f.parent ? fmap.get(f.parent) : root.id });
      for (const b of d.ws.boards || []) {
        const nb = uid(), data = d.boards.find(x => x.id === b.id);
        ws.boards.push({ ...b, id: nb, folder: b.folder ? fmap.get(b.folder) : root.id });
        await DB.put('boards', { id: nb, items: data?.items || [], edges: data?.edges || [], view: data?.view || null });
      }
      await saveWs(); renderTree(); toast('Импортировано в папку «' + root.name + '»');
    } else if (Array.isArray(d.items)) {
      const id = uid(), cur = ws.boards.find(b => b.id === boardId);
      const prep = prepareBoard(d);
      ws.boards.push({ id, name: d.name || file.name.replace(/\.(json|txt)$/i, ''), folder: cur ? cur.folder : null, updated: Date.now() });
      await DB.put('boards', { id, items: prep.items, edges: prep.edges, view: null });
      await saveWs(); await openBoard(id); toast('Доска импортирована');
    } else toast('Это не файл Развилки');
  } catch (err) { toast('Ошибка импорта: ' + err.message); }
});

// ================= Импорт от нейросети: проверка и авторасстановка =================
const NAMED_COLORS = { red: '#e05a5a', blue: '#5b8def', green: '#6cc070', yellow: '#f0c060', purple: '#a78bfa', orange: '#f08a5d', pink: '#e86fb0', gray: '#9aa1ad', grey: '#9aa1ad' };
const KIND_ALIAS = { сцена: 'scene', выбор: 'choice', развилка: 'choice', бой: 'combat', диалог: 'dialog', проверка: 'check', награда: 'loot', концовка: 'ending', battle: 'combat', fight: 'combat', reward: 'loot', end: 'ending' };
function parseLoose(text) {
  try { return JSON.parse(text); } catch {}
  const a = text.indexOf('{'), b = text.lastIndexOf('}'); // ответ нейросети с ```json и пояснениями вокруг
  if (a >= 0 && b > a) return JSON.parse(text.slice(a, b + 1));
  throw new Error('не JSON');
}
function prepareBoard(d) {
  const list = [], ids = new Set();
  for (const r of d.items || []) {
    if (!r || typeof r !== 'object') continue;
    const type = defaults(r.type) ? r.type : (r.title ? 'card' : 'note');
    let id = r.id != null ? String(r.id) : uid(); if (ids.has(id)) id = uid(); ids.add(id);
    const it = { ...r, id, type };
    for (const k of ['title', 'text', 'label']) if (it[k] != null) it[k] = String(it[k]);
    if (type === 'card') { const k = String(it.kind || 'scene').toLowerCase(); it.kind = KIND[k] ? k : KIND_ALIAS[k] || 'scene'; }
    if (type === 'callout' && !CALLOUTS[it.variant]) it.variant = 'remark';
    if (type === 'zone' && NAMED_COLORS[it.color]) it.color = NAMED_COLORS[it.color];
    list.push(it);
  }
  const eds = [];
  for (const e of d.edges || []) {
    if (!e) continue; const from = String(e.from), to = String(e.to);
    if (ids.has(from) && ids.has(to) && from !== to) eds.push({ id: e.id ? String(e.id) : uid(), from, to, label: e.label ? String(e.label) : '', ...(e.kind === 'pin' ? { kind: 'pin', anchor: +e.anchor || 0, anchorText: e.anchorText ? String(e.anchorText) : '' } : {}) });
  }
  const needs = list.some(i => typeof i.x !== 'number' || typeof i.y !== 'number');
  if (needs) autoLayout(list, eds, d.layout === 'vertical' ? 'v' : 'h', d.groups || [], d.name, d.cardWidth, d.checksAside !== false);
  let z = 0;
  for (const it of list) { delete it.group; delete it.attach; it.z = it.type === 'zone' ? -1e6 + (++z) : ++z; }
  return { items: list, edges: eds };
}
// Точная высота блока: собираем его во временном невидимом контейнере и меряем.
let measureHost = null;
function estH(it) {
  if (it.type === 'image') return it.h || 170;
  if (it.type === 'zone') return it.h || 300;
  if (!measureHost) { measureHost = document.createElement('div'); measureHost.style.cssText = 'position:absolute;left:-100000px;top:0;visibility:hidden;pointer-events:none'; document.body.append(measureHost); }
  const full = { ...defaults(it.type), ...it };
  const el = makeEl(full); fill(el, full); el.style.transform = 'none';
  measureHost.append(el); const h = el.offsetHeight; el.remove();
  return h || 60;
}
function measureParaY(it) {
  estH(it); // создаёт измерительный контейнер
  const full = { ...defaults(it.type), ...it }, el = makeEl(full); fill(el, full); el.style.transform = 'none';
  measureHost.append(el); const r = paraYFromEl(el, full, 1); el.remove(); return r;
}
function autoLayout(list, eds, dir, groupsMeta, name, cardWidth, checksAside = true) {
  const W = clamp(+cardWidth || (dir === 'v' ? 400 : 250), 180, 700), byId = new Map(list.map(i => [i.id, i]));
  const cards = list.filter(i => i.type === 'card');
  const isCard = id => byId.get(id)?.type === 'card';
  const grp = id => String(byId.get(id)?.group || '');
  // Для раскладки учитываем переходы внутри руты и из общей линии в руту.
  // Переходы между разными рутами (например «срыв → бой») рисуются, но порядок не ломают.
  const counted = e => isCard(e.from) && isCard(e.to) && (grp(e.from) === grp(e.to) || grp(e.from) === '');
  const out = new Map(cards.map(c => [c.id, []])), preds = new Map(cards.map(c => [c.id, []]));
  for (const e of eds) if (counted(e)) out.get(e.from).push(e.to);
  // ранги — длина самого длинного пути (циклы разрываем)
  const state = new Map(), keep = new Map(cards.map(c => [c.id, []]));
  const dfs = u => { state.set(u, 1); for (const v of out.get(u)) { if (state.get(v) === 1) continue; keep.get(u).push(v); if (!state.get(v)) dfs(v); } state.set(u, 2); };
  for (const c of cards) if (!state.get(c.id)) dfs(c.id);
  for (const [u, vs] of keep) for (const v of vs) preds.get(v).push(u);
  const indeg = new Map(cards.map(c => [c.id, preds.get(c.id).length]));
  const rank = new Map(cards.map(c => [c.id, 0])), queue = cards.filter(c => !indeg.get(c.id)).map(c => c.id);
  while (queue.length) { const u = queue.shift(); for (const v of keep.get(u)) { rank.set(v, Math.max(rank.get(v), rank.get(u) + 1)); indeg.set(v, indeg.get(v) - 1); if (!indeg.get(v)) queue.push(v); } }
  // спутники (ремарки, заметки) — к своей сцене; бесхозные — отдельно
  const sats = new Map(), loose = [];
  for (const it of list) if (it.type !== 'card' && it.type !== 'zone' && it.type !== 'text') {
    if (it.attach && isCard(String(it.attach))) { const a = String(it.attach); if (!sats.has(a)) sats.set(a, []); sats.get(a).push(it); }
    else loose.push(it);
  }
  for (const it of list) if (it.type !== 'zone' && it.type !== 'text') { it.w = W; if (it.type === 'image') it.h = Math.round(W * 0.68); }
  const H = new Map(); const h = it => { if (!H.has(it.id)) H.set(it.id, estH(it)); return H.get(it.id); };
  // проверки из текста сцены — отдельные блоки на полях со стрелкой в свой абзац
  const CW = 250, CGAP = 70;
  const checksOf = c => checksAside ? paraList(c.text).map((p, k) => [p, k]).filter(([p]) => CHECK_RE.test(p)) : [];
  const makeChecks = c => checksOf(c).map(([p, k]) => {
    const ch = { id: uid(), type: 'callout', ...defaults('callout'), variant: 'check', w: CW, text: p.trim().replace(/^Проверка:\s*/, '🎲 ') };
    list.push(ch); eds.push({ id: uid(), from: ch.id, to: c.id, label: '', kind: 'pin', anchor: k, anchorText: p.trim().slice(0, 40) });
    return [ch, k];
  });
  if (dir !== 'v') for (const c of cards) for (const [ch] of makeChecks(c)) { if (!sats.has(c.id)) sats.set(c.id, []); sats.get(c.id).unshift(ch); }
  const bands = ['']; for (const c of cards) { const g = grp(c.id); if (!bands.includes(g)) bands.push(g); }
  const bandOf = new Map(), placed = [];
  const order = new Map(list.map((it, i) => [it.id, i]));
  const SG = 14;
  if (dir === 'v') {
    // Вертикально: каждая рута — свой столбец; ремарки и заметки сцены — справа от неё, стрелки идут чисто.
    const LG = 70, VG = 64, BANDGAP = 130, SIDE = 24;
    const bottom = new Map(); let bandX = 0;
    for (const b of bands) {
      const nodes = cards.filter(c => grp(c.id) === b).sort((p, q) => rank.get(p.id) - rank.get(q.id) || order.get(p.id) - order.get(q.id));
      if (!nodes.length) continue;
      const laneBottom = [], laneOf = new Map();
      const hasSats = nodes.some(n => (sats.get(n.id) || []).length);
      const LEFT = nodes.some(n => checksOf(n).length) ? CW + CGAP : 0;
      const pitch = LEFT + (hasSats ? W + SIDE + W + LG : W + LG);
      for (const n of nodes) {
        const ps = preds.get(n.id);
        let y = 0; for (const p of ps) if (bottom.has(p)) y = Math.max(y, bottom.get(p) + VG);
        const inBand = ps.filter(p => laneOf.has(p)).sort((p, q) => order.get(p) - order.get(q));
        // основное продолжение (самая «дальняя» ветка) остаётся в полосе родителя, боковые ответвления — правее
        let L = 0, mainChild = false;
        if (inBand.length) {
          const par = inBand[0];
          const kids = keep.get(par).filter(v => grp(v) === b).sort((u, v) => rank.get(v) - rank.get(u) || order.get(u) - order.get(v));
          mainChild = kids[0] === n.id;
          L = laneOf.get(par) + (mainChild ? 0 : 1);
        }
        while (laneBottom[L] !== undefined && laneBottom[L] + VG > y) {
          if (mainChild && inBand.length && L === laneOf.get(inBand[0])) { y = laneBottom[L] + VG; break; }
          L++;
        }
        laneOf.set(n.id, L);
        n.x = bandX + L * pitch + LEFT; n.y = y; placed.push(n); bandOf.set(n.id, b);
        let cy = -Infinity;
        const chk = makeChecks(n);
        if (chk.length) {
          const py = measureParaY(n);
          for (const [ch, k] of chk) {
            ch.x = n.x - CW - CGAP; ch.y = Math.max(y + (py && py[k] != null ? py[k] : 30) - 22, cy + 12);
            cy = ch.y + h(ch); placed.push(ch); bandOf.set(ch.id, b);
          }
        }
        let sy = y;
        for (const s of sats.get(n.id) || []) { s.x = n.x + W + SIDE; s.y = sy; sy += h(s) + SG; placed.push(s); bandOf.set(s.id, b); }
        const yy = Math.max(y + h(n), sy - SG, cy);
        laneBottom[L] = yy; bottom.set(n.id, y + h(n));
        // следующая сцена этой линии не должна заезжать на заметки справа
        if (Math.max(sy - SG, cy) > y + h(n)) laneBottom[L] = Math.max(sy - SG, cy);
      }
      bandX += (Math.max(...laneOf.values()) + 1) * pitch - LG + BANDGAP;
    }
    let yy = 0;
    for (const it of loose) { it.x = bandX; it.y = yy; yy += h(it) + SG + 10; placed.push(it); bandOf.set(it.id, '__loose'); }
    if (loose.length) bands.push('__loose');
  } else {
    // Горизонтально: руты — полосами друг под другом.
    const GAP = 110, ROW = 48, BAND = 130;
    const slots = new Map();
    const put = (b, r, it) => { if (!slots.has(b)) slots.set(b, new Map()); const m = slots.get(b); if (!m.has(r)) m.set(r, []); m.get(r).push(it); bandOf.set(it.id, b); };
    for (const c of cards) { put(grp(c.id), rank.get(c.id), c); for (const s of sats.get(c.id) || []) put(grp(c.id), rank.get(c.id), s); }
    loose.forEach((it, i) => put('__loose', i, it)); if (loose.length) bands.push('__loose');
    let y = 0;
    for (const b of bands) {
      const cols = slots.get(b); if (!cols || !cols.size) continue;
      const rowH = [];
      for (const col of cols.values()) col.forEach((it, i) => { rowH[i] = Math.max(rowH[i] || 0, h(it)); });
      for (const [r, col] of cols) { let yy = y; col.forEach((it, i) => { it.x = r * (W + GAP); it.y = yy; yy += rowH[i] + ROW; placed.push(it); }); }
      y += rowH.reduce((a, v) => a + v + ROW, 0) - ROW + BAND;
    }
  }
  // зоны вокруг рут
  const meta = new Map((groupsMeta || []).map(g => [String(g.name), g]));
  let ci = 0;
  for (const b of bands) {
    if (!b) continue;
    const its = placed.filter(i => bandOf.get(i.id) === b); if (!its.length) continue;
    const x0 = Math.min(...its.map(i => i.x)) - 36, y0 = Math.min(...its.map(i => i.y)) - 44;
    const x1 = Math.max(...its.map(i => i.x + i.w)) + 36, y1 = Math.max(...its.map(i => i.y + h(i))) + 36;
    const g = meta.get(b), named = g && (NAMED_COLORS[g.color] || (/^#/.test(g.color || '') && g.color));
    list.push({ id: uid(), type: 'zone', ...defaults('zone'), x: x0, y: y0, w: x1 - x0, h: y1 - y0,
      color: b === '__loose' ? '#9aa1ad' : named || ZONE_COLORS[[2, 0, 6, 1, 4, 5, 3][ci++ % 7]], label: b === '__loose' ? 'Без привязки' : b });
  }
  // заголовок и свободный текст — сверху
  let top = Math.min(0, ...placed.map(i => i.y)) - 80;
  const texts = list.filter(i => i.type === 'text' && (typeof i.x !== 'number' || typeof i.y !== 'number'));
  if (name && !texts.length) { const t = { id: uid(), type: 'text', ...defaults('text'), text: String(name), size: 40, bold: true, font: 'serif', w: 900 }; list.push(t); texts.push(t); }
  for (const t of texts.reverse()) { t.w = t.w || 900; top -= h(t) + 10; t.x = 0; t.y = top; }
}

// ================= Экспорт доски в Word (.docx) =================
// Собираем документ сами: .docx — это zip с XML внутри. Без библиотек и интернета.
const CRC_T = (() => { const t = new Uint32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
const crc32 = b => { let c = 0xFFFFFFFF; for (let i = 0; i < b.length; i++) c = CRC_T[(c ^ b[i]) & 0xFF] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; };
function zipStore(files) { // files: [{name, text}] → Blob (zip без сжатия)
  const enc = new TextEncoder(), parts = [], central = []; let off = 0;
  for (const f of files) {
    const name = enc.encode(f.name), data = enc.encode(f.text), crc = crc32(data);
    const h = new DataView(new ArrayBuffer(30));
    h.setUint32(0, 0x04034b50, true); h.setUint16(4, 20, true); h.setUint16(6, 0x0800, true); h.setUint16(8, 0, true);
    h.setUint32(14, crc, true); h.setUint32(18, data.length, true); h.setUint32(22, data.length, true); h.setUint16(26, name.length, true);
    parts.push(h, name, data);
    const c = new DataView(new ArrayBuffer(46));
    c.setUint32(0, 0x02014b50, true); c.setUint16(4, 20, true); c.setUint16(6, 20, true); c.setUint16(8, 0x0800, true);
    c.setUint32(16, crc, true); c.setUint32(20, data.length, true); c.setUint32(24, data.length, true); c.setUint16(28, name.length, true); c.setUint32(42, off, true);
    central.push(c, name); off += 30 + name.length + data.length;
  }
  const csize = central.reduce((a, p) => a + p.byteLength, 0);
  const e = new DataView(new ArrayBuffer(22));
  e.setUint32(0, 0x06054b50, true); e.setUint16(8, files.length, true); e.setUint16(10, files.length, true); e.setUint32(12, csize, true); e.setUint32(16, off, true);
  return new Blob([...parts, ...central, e], { type: 'application/vnd.openxmlformats-officedocument.wordprocessingml.document' });
}
const xesc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
// плашки — цвета как в исходном документе сценария
const PLATE = {
  speech: { fill: 'F5EFFB', border: '7A3FA8', name: '5A1E78', text: '1E1E1E', i: true },
  dm:     { fill: 'E9F4EC', border: '2E8B57', text: '0E633B', i: true },
  check:  { fill: 'FDECEC', border: 'C62828', text: 'B41E1E', b: true },
  note:   { fill: 'F1F1F1', border: '8C8C8C', text: '505050', i: true },
  vn:     { fill: '1E1B2E', border: '9B6BCC', text: 'A9A3B8', name: 'C9A6FF', speech: 'F2EEF8', i: true },
  mech:   { fill: 'EDF1F8', border: '1F3864', text: '1E1E1E' },
  todo:   { fill: 'FFF4DE', border: 'C58A1C', text: '85510B', i: true },
  sticky: { fill: 'FFF7D1', border: 'D9B02F', text: '1E1E1E' },
  read:   { fill: 'EAF1FD', border: '3D6FD1', text: '1E1E1E', i: true },
  warn:   { fill: 'FDECEC', border: 'C62828', text: 'B41E1E' },
};
function run(text, o = {}) {
  const pr = (o.b ? '<w:b/>' : '') + (o.i ? '<w:i/>' : '') + (o.u ? '<w:u w:val="single"/>' : '') + (o.color ? `<w:color w:val="${o.color}"/>` : '') + `<w:sz w:val="${o.sz || 21}"/>`;
  return String(text).split('\n').map((ln, k) => (k ? `<w:r><w:rPr>${pr}</w:rPr><w:br/></w:r>` : '') + `<w:r><w:rPr>${pr}</w:rPr><w:t xml:space="preserve">${xesc(ln)}</w:t></w:r>`).join('');
}
function para(runs, o = {}) {
  let pr = '';
  if (o.style) pr += `<w:pStyle w:val="${o.style}"/>`;
  if (o.keep) pr += '<w:keepNext/>';
  if (o.plate) { const p = PLATE[o.plate]; pr += `<w:pBdr><w:left w:val="single" w:sz="24" w:space="10" w:color="${p.border}"/></w:pBdr><w:shd w:val="clear" w:color="auto" w:fill="${p.fill}"/><w:spacing w:before="100" w:after="100" w:line="276" w:lineRule="auto"/><w:ind w:left="240" w:right="240"/>`; }
  else if (!o.style) pr += '<w:spacing w:before="0" w:after="160" w:line="300" w:lineRule="auto"/>';
  if (o.align) pr += `<w:jc w:val="${o.align}"/>`;
  return `<w:p><w:pPr>${pr}</w:pPr>${runs}</w:p>`;
}
// Абзац карточки → плашка по метке, которую ставит импорт (🗣, ▸ ДМ:, 🎲, ◆ …)
function blockXml(t) {
  t = t.trim(); if (!t) return '';
  let m;
  if ((m = t.match(/^🗣\s*([^:]{1,40}):\s*([\s\S]*)$/))) { const P = PLATE.speech; return para(run(m[1] + ': ', { b: true, color: P.name }) + run(m[2].replace(/^«|»$/g, ''), { i: true, color: P.text }), { plate: 'speech' }); }
  if ((m = t.match(/^(?:▸\s*)?ДМ:\s*([\s\S]*)$/)) || (m = t.match(/^▸\s*([\s\S]*)$/))) return para(run('▸  ' + m[1], { i: true, color: PLATE.dm.text }), { plate: 'dm' });
  if ((m = t.match(/^Проверка:\s*([\s\S]*)$/))) t = '🎲 ' + m[1];
  if ((m = t.match(/^Механика:\s*([\s\S]*)$/))) t = '◆ ' + m[1];
  if ((m = t.match(/^(?:⚠\s*)?Важно:\s*([\s\S]*)$/))) return para(run('Важно: ', { b: true, color: PLATE.warn.text }) + run(m[1], { color: PLATE.warn.text }), { plate: 'warn' });
  if (/^(🎲|⚡)/.test(t)) return para(run(t, { b: true, color: PLATE.check.text }), { plate: 'check' });
  if (/^◆/.test(t)) return para(run(t, { color: PLATE.mech.text }), { plate: 'mech' });
  if (/^\/\//.test(t)) return para(run(t, { i: true, color: PLATE.note.text }), { plate: 'note' });
  if (/^📝/.test(t)) return para(run(t.replace(/^📝\s*/, ''), { i: true, color: PLATE.todo.text }), { plate: 'todo' });
  if (/^\([\s\S]*\)$/.test(t)) return para(run(t.slice(1, -1), { i: true, color: PLATE.vn.text }), { plate: 'vn' });
  if ((m = t.match(/^([А-ЯЁA-Z][а-яёa-z]{1,20}):\s+([\s\S]{1,300})$/)) && !t.includes('\n')) { const P = PLATE.vn; return para(run(m[1].toUpperCase() + '  ', { b: true, color: P.name }) + run(m[2], { color: P.speech }), { plate: 'vn' }); }
  return para(run(t, { color: '1E1E1E' }));
}
const textXml = s => String(s || '').split(/\n{2,}/).map(blockXml).join('');

function boardToDocx() {
  const all = [...items.values()];
  const cards = all.filter(i => i.type === 'card');
  const zones = all.filter(i => i.type === 'zone');
  const others = all.filter(i => i.type !== 'card' && i.type !== 'zone');
  const area = z => z.w * z.h;
  const zoneOf = c => { const cx = c.x + c.w / 2, cy = c.y + Math.min(c.h, 60) / 2; return zones.filter(z => cx >= z.x && cx <= z.x + z.w && cy >= z.y && cy <= z.y + z.h).sort((a, b) => area(a) - area(b))[0] || null; };
  // заголовок — самый крупный свободный текст
  const texts = others.filter(o => o.type === 'text').sort((a, b) => (b.size || 0) - (a.size || 0));
  const titleIt = texts.length && (texts[0].size || 0) >= 24 ? texts[0] : null;
  const b = ws.boards.find(x => x.id === boardId);
  const title = titleIt ? titleIt.text : (b ? b.name : 'Доска');
  // порядок: ранги по стрелкам, затем сверху вниз, слева направо
  const out = new Map(cards.map(c => [c.id, []])), indeg = new Map(cards.map(c => [c.id, 0]));
  for (const e of edges.values()) if (out.has(e.from) && out.has(e.to)) out.get(e.from).push(e.to);
  const state = new Map(), keep = new Map(cards.map(c => [c.id, []]));
  const dfs = u => { state.set(u, 1); for (const v of out.get(u)) { if (state.get(v) === 1) continue; keep.get(u).push(v); if (!state.get(v)) dfs(v); } state.set(u, 2); };
  for (const c of [...cards].sort((p, q) => p.y - q.y || p.x - q.x)) if (!state.get(c.id)) dfs(c.id);
  for (const vs of keep.values()) for (const v of vs) indeg.set(v, indeg.get(v) + 1);
  const rank = new Map(cards.map(c => [c.id, 0])), q = cards.filter(c => !indeg.get(c.id)).map(c => c.id);
  while (q.length) { const u = q.shift(); for (const v of keep.get(u)) { rank.set(v, Math.max(rank.get(v), rank.get(u) + 1)); indeg.set(v, indeg.get(v) - 1); if (!indeg.get(v)) q.push(v); } }
  const byOrder = (p, r) => rank.get(p.id) - rank.get(r.id) || p.y - r.y || p.x - r.x;
  // внутри руты — ветка целиком, потом следующая (а не вперемешку по уровням)
  const branchOrder = cs => {
    const ids = new Set(cs.map(c => c.id)), pend = new Map(cs.map(c => [c.id, 0]));
    for (const c of cs) for (const v of keep.get(c.id)) if (ids.has(v)) pend.set(v, pend.get(v) + 1);
    const res = [], stack = cs.filter(c => !pend.get(c.id)).sort(byOrder).reverse();
    while (stack.length) {
      const c = stack.pop(); res.push(c);
      const kids = keep.get(c.id).filter(v => ids.has(v)).map(v => items.get(v)).sort((p, r) => p.x - r.x || p.y - r.y);
      for (const k of kids.reverse()) { pend.set(k.id, pend.get(k.id) - 1); if (!pend.get(k.id)) stack.push(k); }
    }
    for (const c of cs.sort(byOrder)) if (!res.includes(c)) res.push(c);
    return res;
  };
  const groups = new Map([[null, []]]); for (const z of [...zones].sort((p, r) => p.x - r.x || p.y - r.y)) groups.set(z, []);
  for (const c of cards) groups.get(zoneOf(c)).push(c);
  // ремарки, заметки, картинки — к ближайшей сцене
  const dist = (a, c) => Math.hypot(Math.max(0, c.x - (a.x + a.w), a.x - (c.x + c.w)), Math.max(0, c.y - (a.y + a.h), a.y - (c.y + c.h)));
  const satOf = new Map(), loose = [];
  const pinOf = new Map([...edges.values()].filter(e => e.kind === 'pin').map(e => [e.from, e]));
  for (const o of others) {
    if (o === titleIt || (o.type === 'text' && !String(o.text || '').trim())) continue;
    // проверка на полях, текст которой уже есть в сцене, — в документе не дублируем
    if (o.type === 'callout' && pinOf.has(o.id)) {
      const c = items.get(pinOf.get(o.id).to), core = String(o.text || '').replace(/^\s*(🎲|⚡)\s*/, '').trim().slice(0, 30);
      if (c && core && String(c.text || '').includes(core)) continue;
      if (c) { if (!satOf.has(c.id)) satOf.set(c.id, []); satOf.get(c.id).push(o); continue; }
    }
    let best = null, bd = Infinity; for (const c of cards) { const d = dist(o, c); if (d < bd) { bd = d; best = c; } }
    if (best && bd < 420) { if (!satOf.has(best.id)) satOf.set(best.id, []); satOf.get(best.id).push(o); } else loose.push(o);
  }
  const cardTitle = c => (c.title || '').trim() || 'Без названия';
  const where = new Map(); for (const [z, cs] of groups) for (const c of cs) where.set(c.id, z);
  let body = '';
  body += para(run(title, { b: true, sz: 48, color: '1F3864' }), { style: 'Title' });
  body += para(run('Экспорт из «Развилки» · ' + new Date().toLocaleDateString('ru'), { i: true, sz: 18, color: '8C8C8C' }));
  body += para(run('Плашки: ', { b: true, sz: 18, color: '505050' }) + run('реплика персонажа · заметка ДМ · проверка · механика боя · формат новеллы · служебная пометка · TODO · заметка с холста', { sz: 18, color: '505050' }));
  const satXml = o => (o.spoiler ? para(run('🔒 Спойлер — не показывать игрокам', { sz: 17, b: true, color: '8C8C8C' }), { keep: true }) : '') + satXml0(o);
  const satXml0 = o => {
    if (o.type === 'image') return para(run('🖼 Картинка: ', { b: true, color: '505050' }) + run(o.src || '', { color: '3D6FD1', u: true }), { plate: 'note' });
    if (o.type === 'callout') { const v = o.variant === 'read' ? 'read' : o.variant === 'warn' ? 'warn' : o.variant === 'check' ? 'check' : 'dm'; const head = (CALLOUTS[o.variant] || CALLOUTS.remark).name;
      const parts = String(o.text || '').split(/\n{2,}/);
      return para(run(head.toUpperCase(), { b: true, sz: 17, color: PLATE[v].border }), { plate: v, keep: true }) + parts.map(p => /^(🗣|▸|🎲|◆|\/\/|📝)/.test(p.trim()) ? blockXml(p) : para(run(p, { i: PLATE[v].i, color: PLATE[v].text }), { plate: v })).join(''); }
    if (o.type === 'note') return String(o.text || '').split(/\n{2,}/).map((p, k) => para(run(p, { b: k === 0 && p.length < 80 && p === p.toUpperCase(), color: PLATE.sticky.text }), { plate: 'sticky' })).join('');
    return textXml(o.text);
  };
  const emitCard = c => {
    const k = KIND[c.kind] || KINDS[0];
    let x = para(run(cardTitle(c), { color: '1F3864' }) + run('   ' + k.name.toUpperCase(), { sz: 16, color: k.color.slice(1).toUpperCase(), b: true }) + (c.spoiler ? run('   🔒 СПОЙЛЕР', { sz: 16, color: '8C8C8C', b: true }) : ''), { style: 'Heading3', keep: true });
    x += textXml(c.text);
    for (const s of satOf.get(c.id) || []) x += satXml(s);
    const outs = [...edges.values()].filter(e => e.from === c.id).map(e => ({ e, t: items.get(e.to) })).filter(o => o.t);
    if (outs.length > 1 || outs.some(o => o.e.label || where.get(o.t.id) !== where.get(c.id))) {
      x += para(run('Переходы:', { b: true, sz: 19, color: '505050' }), { keep: true });
      for (const { e, t } of outs) {
        const z = where.get(t.id), zn = z && z !== where.get(c.id) ? ` (${z.label || 'зона'})` : '';
        x += para(run('→ ', { b: true, color: '1F3864' }) + (e.label ? run(e.label + ': ', { i: true, color: '505050' }) : '') + run(cardTitle(t) + zn, { b: true, color: '1F3864' }));
      }
    }
    return x;
  };
  for (const [z, cs] of groups) {
    if (!cs.length) continue;
    if (z) body += para(run(z.label || 'Зона', { color: '1F3864' }), { style: 'Heading2', keep: true });
    else if (groups.size > 1) body += para(run('Общая линия', { color: '1F3864' }), { style: 'Heading2', keep: true });
    for (const c of branchOrder(cs)) body += emitCard(c);
  }
  if (loose.length) { body += para(run('Прочее', { color: '1F3864' }), { style: 'Heading2', keep: true }); for (const o of loose) body += satXml(o); }
  const doc = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><w:body>${body}<w:sectPr><w:pgSz w:w="11906" w:h="16838"/><w:pgMar w:top="1134" w:right="1134" w:bottom="1134" w:left="1134" w:header="709" w:footer="709" w:gutter="0"/></w:sectPr></w:body></w:document>`;
  const hs = (id, name, sz, before, color = '1F3864', lvl) => `<w:style w:type="paragraph" w:styleId="${id}"><w:name w:val="${name}"/><w:basedOn w:val="Normal"/><w:next w:val="Normal"/><w:qFormat/><w:pPr><w:keepNext/><w:spacing w:before="${before}" w:after="100"/>${lvl !== undefined ? `<w:outlineLvl w:val="${lvl}"/>` : ''}</w:pPr><w:rPr><w:b/><w:color w:val="${color}"/><w:sz w:val="${sz}"/></w:rPr></w:style>`;
  const styles = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><w:styles xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"><w:docDefaults><w:rPrDefault><w:rPr><w:rFonts w:ascii="Segoe UI" w:hAnsi="Segoe UI" w:cs="Segoe UI" w:eastAsia="Segoe UI"/><w:sz w:val="21"/><w:lang w:val="ru-RU"/></w:rPr></w:rPrDefault><w:pPrDefault><w:pPr><w:spacing w:after="120" w:line="276" w:lineRule="auto"/></w:pPr></w:pPrDefault></w:docDefaults><w:style w:type="paragraph" w:default="1" w:styleId="Normal"><w:name w:val="Normal"/><w:qFormat/></w:style>${hs('Title', 'Title', 48, 0)}${hs('Heading1', 'heading 1', 36, 360, '1F3864', 0)}${hs('Heading2', 'heading 2', 36, 520, '1F3864', 1)}${hs('Heading3', 'heading 3', 26, 300, '1F3864', 2)}</w:styles>`;
  const files = [
    { name: '[Content_Types].xml', text: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/><Override PartName="/word/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.styles+xml"/></Types>' },
    { name: '_rels/.rels', text: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/></Relationships>' },
    { name: 'word/_rels/document.xml.rels', text: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>' },
    { name: 'word/document.xml', text: doc },
    { name: 'word/styles.xml', text: styles },
  ];
  return { blob: zipStore(files), name: (b ? b.name : title) };
}
async function exportDocx() {
  stopEdit();
  if (!items.size) { toast('Доска пустая — экспортировать нечего'); return; }
  const { blob, name } = boardToDocx();
  if (await saveBlob(name, blob, 'docx', 'Документ Word') && !DESKTOP) toast('Документ Word сохранён в загрузки');
}

// ================= Отдельное окно =================
// Лучший вариант — установить как приложение (Chrome, Edge, Яндекс): своё окно без адресной строки и вкладок,
// размер и место окна браузер запоминает сам. Если установка недоступна — всплывающее окно того же размера.
let installEvt = null;
const STANDALONE = matchMedia('(display-mode: standalone)').matches || matchMedia('(display-mode: window-controls-overlay)').matches || navigator.standalone === true;
window.addEventListener('beforeinstallprompt', e => { e.preventDefault(); installEvt = e; $('#installBtn')?.classList.remove('hidden'); });
window.addEventListener('appinstalled', () => { installEvt = null; toast('Установлено. Запускайте «Развилку» из меню Пуск или с рабочего стола.', 5000); });
if (STANDALONE || MOBILE || DESKTOP || new URLSearchParams(location.search).has('popup')) $('#winBtn').remove();
async function openWindow() {
  await saveNow();
  const w = window.open(location.pathname + '?popup', 'razvilka-' + TAB,
    `popup=yes,width=${Math.max(360, Math.round(outerWidth * 0.5))},height=${Math.max(480, outerHeight)},left=${screenX + Math.round(outerWidth * 0.5)},top=${screenY}`);
  if (!w) { toast('Браузер заблокировал окно — разрешите всплывающие окна для этого сайта.', 5000); return; }
  toast('Окно открыто. Эта вкладка остаётся — правки из окна появятся здесь сами.', 4500);
}
async function installApp() {
  if (!installEvt) { toast('Установка недоступна: откройте сайт в Chrome, Edge или Яндекс.Браузере, либо приложение уже установлено.', 5000); return; }
  installEvt.prompt();
  await installEvt.userChoice; installEvt = null; $('#installBtn')?.classList.add('hidden');
}

// ================= Подсказка «где сохранено» =================
const fmtBytes = n => n < 1024 * 1024 ? Math.max(1, Math.round(n / 1024)) + ' КБ' : (n / 1024 / 1024).toFixed(1) + ' МБ';
async function showSaveTip() {
  const tip = $('#saveTip'), r = saveState.getBoundingClientRect();
  let usage = '', persisted = null;
  try { const est = await navigator.storage.estimate(); usage = fmtBytes(est.usage || 0); } catch {}
  try { persisted = await navigator.storage.persisted(); } catch {}
  const t = lastSavedAt ? lastSavedAt.toLocaleTimeString('ru', { hour: '2-digit', minute: '2-digit', second: '2-digit' }) : null;
  tip.innerHTML = DESKTOP && DB.db ? `
    <b>Где хранятся данные</b>
    <p class="ok">Сохранено <b>в приложении на этом компьютере</b>${t ? ', последний раз в ' + t : ''}. Каждое изменение записывается сразу.</p>
    <p class="no">В интернет ничего не отправляется.</p>
    ${backupDir ? `<p class="ok">Резервные копии всей кампании: <b>${xesc(backupDir)}</b>${lastBackupAt ? ', последняя в ' + lastBackupAt.toLocaleTimeString('ru', { hour: '2-digit', minute: '2-digit' }) : ''}. Хранятся копии за 14 последних дней.</p>`
      : `<p class="warn">Резервные копии выключены. Включите их внизу боковой панели — тогда кампания будет ещё и лежать файлом в выбранной папке.</p>`}
    <p>Доски приложения и сайта в браузере — отдельные. Перенос — «Экспорт всего» → «Импорт из файла».</p>
    <small>${usage ? 'Занято: ' + usage : ''}</small>`
    : DB.db ? `
    <b>Где хранятся данные</b>
    <p class="ok">Сохранено <b>в этом браузере на этом устройстве</b>${t ? ', последний раз в ' + t : ''}. Каждое изменение записывается сразу.</p>
    <p class="no">На сервер и в интернет ничего не отправляется. GitHub хранит только саму программу, не ваши доски.</p>
    <p>Другие устройства и браузеры этих досок не видят. Чтобы перенести или сделать резервную копию — «Экспорт всего» в боковой панели.</p>
    <p class="warn">Очистка истории / данных сайтов в браузере удалит доски.</p>
    <small>${usage ? 'Занято: ' + usage + ' · ' : ''}${persisted === null ? '' : persisted ? 'браузер не будет чистить сам' : 'браузер может почистить при нехватке места'}</small>`
    : `<b>Сохранение не работает</b><p class="warn">Хранилище браузера недоступно (например, режим инкогнито). Всё пропадёт при закрытии вкладки — сделайте «Экспорт всего».</p>`;
  tip.classList.remove('hidden');
  tip.style.left = Math.max(8, Math.min(r.left - 40, innerWidth - tip.offsetWidth - 8)) + 'px';
  tip.style.top = (r.bottom + 14) + 'px';
}
saveState.addEventListener('mouseenter', showSaveTip);
saveState.addEventListener('mouseleave', () => $('#saveTip').classList.add('hidden'));
saveState.addEventListener('click', () => $('#saveTip').classList.contains('hidden') ? showSaveTip() : $('#saveTip').classList.add('hidden'));

// ================= Приложение для ПК (Tauri) =================
// В приложении: «Сохранить как…» вместо загрузок, внешние ссылки — в браузере, автокопии в выбранную папку.
async function saveBlob(name, blob, ext, label) {
  name = String(name).replace(/[\\/:*?"<>|]+/g, '_');
  if (!DESKTOP) {
    const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name + '.' + ext;
    document.body.append(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(a.href), 3000);
    return true;
  }
  try {
    const path = await tauriInvoke('plugin:dialog|save', { options: { defaultPath: name + '.' + ext, filters: [{ name: label || ext, extensions: [ext] }] } });
    if (!path) return false;
    await tauriInvoke('write_file', { path, data: Array.from(new Uint8Array(await blob.arrayBuffer())) });
    toast('Сохранено: ' + path, 4500); return true;
  } catch (err) { toast('Не удалось сохранить файл: ' + err, 6000); return false; }
}
function openExternal(url) {
  if (DESKTOP) tauriInvoke('plugin:opener|open_url', { url }).catch(() => toast('Не удалось открыть ссылку'));
  else window.open(url, '_blank', 'noopener');
}
// ---- резервные копии в папку (например, в Яндекс.Диск / OneDrive — тогда они ещё и синхронизируются)
function scheduleBackup() { if (!DESKTOP || !backupDir) return; clearTimeout(backupTimer); backupTimer = setTimeout(doBackup, 5000); }
async function doBackup(manual) {
  clearTimeout(backupTimer); backupTimer = null;
  if (!DESKTOP || !backupDir) return;
  try {
    const boards = await DB.all('boards');
    const now = new Date(), day = now.toISOString().slice(0, 10);
    await tauriInvoke('write_backup', { dir: backupDir, latestName: 'Развилка — кампания.json', dailyName: `Развилка — бэкап ${day}.json`,
      contents: JSON.stringify({ app: 'razvilka', kind: 'workspace', version: 1, ws, boards }), keep: 14 });
    lastBackupAt = now; renderBackupBtn();
    if (manual) toast('Копия сохранена в «' + backupDir + '»', 4000);
  } catch (err) { toast('Резервная копия не записалась: ' + err, 6000); }
}
function renderBackupBtn() {
  const b = $('#backupBtn'); if (!b) return;
  const folder = backupDir ? backupDir.split(/[\\/]/).filter(Boolean).pop() : '';
  b.textContent = backupDir ? `Резервные копии: ${folder}` + (lastBackupAt ? ` · ${lastBackupAt.toLocaleTimeString('ru', { hour: '2-digit', minute: '2-digit' })}` : '') : 'Резервные копии: выключены';
  b.title = backupDir || 'Выберите папку — приложение будет само сохранять туда копию всей кампании';
}
async function chooseBackupDir() {
  try {
    const dir = await tauriInvoke('plugin:dialog|open', { options: { directory: true, multiple: false, title: 'Папка для резервных копий Развилки' } });
    if (!dir) return;
    backupDir = Array.isArray(dir) ? dir[0] : dir;
    try { localStorage.setItem(BK_KEY, backupDir); } catch {}
    renderBackupBtn(); await doBackup(true);
  } catch (err) { toast('Не удалось выбрать папку: ' + err, 5000); }
}
let importMode = 'add';
function backupMenu(btnEl) {
  const r = btnEl.getBoundingClientRect();
  const opts = [{ label: backupDir ? 'Сменить папку…' : 'Выбрать папку…', fn: chooseBackupDir }];
  if (backupDir) opts.push({ label: 'Сохранить копию сейчас', fn: () => doBackup(true) },
    { label: 'Выключить копии', fn: () => { backupDir = ''; try { localStorage.removeItem(BK_KEY); } catch {} renderBackupBtn(); } });
  opts.push({ label: 'Восстановить из копии (заменить всё)…', danger: true, fn: () => { importMode = 'restore'; $('#importFile').click(); } });
  showMenu(r.right + 8, r.top - 60, opts, 'Резервные копии');
}
async function restoreWorkspace(d) {
  if (!await popAsk({ anchor: $('#backupBtn'), title: 'Заменить всё содержимое?', input: false, danger: true, ok: 'Заменить',
    message: `Все текущие папки и доски заменятся содержимым копии (${(d.boards || []).length} досок). Отменить это будет нельзя.` })) return;
  stopEdit(); clearTimeout(saveTimer);
  for (const b of await DB.all('boards')) await DB.del('boards', b.id);
  for (const b of d.boards) await DB.put('boards', b);
  ws = { ...d.ws, id: 'ws' }; await DB.put('meta', ws);
  boardId = null; contentChanged = false;
  const start = ws.boards.find(b => b.id === ws.current) ? ws.current : ws.boards[0]?.id;
  if (start) await openBoard(start);
  renderTree(); toast('Кампания восстановлена из копии', 3000);
}
if (DESKTOP) {
  const foot = $('.sbfoot');
  const b = document.createElement('button'); b.id = 'backupBtn'; b.className = 'btn ghost';
  b.addEventListener('click', () => backupMenu(b));
  foot.insertBefore(b, foot.firstChild); renderBackupBtn();
}

// ================= Версия =================
async function showVersion() {
  let v = APP_VERSION, where = 'веб-версия';
  if (DESKTOP) { where = 'приложение для ПК'; try { v = await tauriInvoke('plugin:app|version'); } catch {} }
  const text = `Развилка ${v} · ${where}`;
  for (const el of document.querySelectorAll('.app-version')) el.textContent = text;
}
showVersion();

// ================= Кнопки =================
const actions = {
  sidebar: () => toggleSidebar(),
  insert: b => { const r = b.getBoundingClientRect(); const wp = toWorld({ x: viewport.clientWidth / 2, y: viewport.clientHeight * 0.45 }); lastPointer = null; showInsertMenu({ x: r.left, y: r.bottom + 6 }, wp); },
  undo, redo, fit,
  boxmode: () => { boxMode = !boxMode; updateUI(); toast(boxMode ? 'Режим рамки: тяните по пустому месту, чтобы выделить' : 'Режим рамки выключен', 1800); },
  search: () => $('#searchBox').classList.contains('hidden') ? openSearch() : closeSearch(),
  newFolder: b => newFolder(null, sideAnchor(b)),
  newBoard: b => newBoard(undefined, undefined, sideAnchor(b)),
  exportAll, importAll: () => $('#importFile').click(), exportDocx,
  aiGuide: () => {
    saveBlob('Развилка — инструкция для нейросети', new Blob([window.RAZVILKA_AI_GUIDE || ''], { type: 'text/markdown' }), 'md', 'Markdown');
    if (!DESKTOP) toast('Отдайте нейросети этот файл и документ сценария. Её ответ сохраните как .json и загрузите через «Импорт из файла».', 7000);
  },
  theme: toggleTheme, help: () => toggleHelp(), accent: b => accentMenu(b),
  window: openWindow, install: installApp, reattach: () => location.reload(),
};
document.addEventListener('click', e => {
  const b = e.target.closest('[data-act]'); if (!b || b.disabled) return;
  actions[b.dataset.act]?.(b);
});

// ================= Уведомления =================
let toastTimer;
function toast(msg, ms = 3000) {
  const t = $('#toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), ms);
}

// ================= Пример =================
function sampleBoard() {
  const K = (id, x, y, kind, title, text = '') => ({ id, type: 'card', ...defaults('card'), x, y, kind, title, text });
  const it = [
    { id: 'z1', type: 'zone', ...defaults('zone'), x: 2140, y: -640, w: 1290, h: 400, color: '#e05a5a', label: 'Рута 1 — Атака' },
    { id: 'z2', type: 'zone', ...defaults('zone'), x: 2140, y: -150, w: 2170, h: 360, color: '#5b8def', label: 'Рута 2 — Диалог + помощь' },
    { id: 'z3', type: 'zone', ...defaults('zone'), x: 2140, y: 300, w: 700, h: 230, color: '#9aa1ad', label: 'Рута 3 — Уйти' },
    { id: 't0', type: 'text', ...defaults('text'), x: 0, y: -260, w: 900, size: 44, bold: true, font: 'serif', text: 'Партия 1 — Ведьма Акри' },
    { id: 't1', type: 'text', ...defaults('text'), x: 0, y: -185, w: 900, size: 16, color: '#9aa1ad', text: 'Пример доски. Двойной клик по пустому месту — меню вставки. Ссылку на картинку можно просто вставить через Ctrl+V.' },
    K('n1', 0, 0, 'scene', 'Завязка — Гильдия Авантюристов'),
    K('n2', 320, 0, 'dialog', 'Встреча с виноторговцем'),
    K('n3', 640, 0, 'scene', 'Приезд на винодельню'),
    K('n4', 960, 0, 'scene', 'Путь к замку'),
    K('n5', 1280, 0, 'scene', 'Замок'),
    K('n6', 1600, 0, 'scene', 'Библиотека — встреча с Акри'),
    K('n7', 1820, 200, 'choice', 'Подход к Акри', 'Тишина → Притяжение → Обрыв'),
    K('a1', 2200, -560, 'combat', 'Начало боя'),
    K('a2', 2500, -560, 'combat', 'Фаза 1: Воздух', '> 50% ХП'),
    K('a3', 2800, -560, 'combat', 'Фаза 2: Земля', '< 50% ХП'),
    K('a4', 3120, -600, 'ending', 'Победа (убить)'),
    K('a5', 3120, -420, 'ending', 'Поражение'),
    K('b1', 2200, -70, 'dialog', 'Разговор'),
    K('b2', 2500, -70, 'check', 'Трещины 1–3', 'Слова-триггеры → риск срыва'),
    K('b3', 2800, -70, 'scene', 'Ритуал'),
    K('b4', 3100, -70, 'combat', 'Гули атакуют — побег'),
    K('b5', 3400, -70, 'combat', 'Рыцарь у выхода'),
    K('b6', 3700, -70, 'ending', 'Финал руты 2'),
    K('c1', 2200, 380, 'scene', 'Уйти'),
    K('c2', 2520, 380, 'ending', 'Последствия в будущих партиях'),
    { id: 'r1', type: 'callout', ...defaults('callout'), x: 1530, y: 380, variant: 'remark', text: 'Здесь игроки сами выбирают руту — не подталкивайте.' },
    { id: 'r2', type: 'callout', ...defaults('callout'), x: 1600, y: -200, w: 300, variant: 'read', font: 'serif', italic: true, text: 'Текст для зачитывания игрокам — вставьте из сценария.' },
    { id: 'r3', type: 'note', ...defaults('note'), x: 3460, y: 300, text: 'Награды:\n— мирный путь: каждый выбирает одно\n— победа: трофеи Акри' },
  ];
  let z = 0; for (const x of it) x.z = x.type === 'zone' ? -1e6 + (++z) : ++z;
  const E = (from, to, label = '') => ({ id: from + to, from, to, label });
  const ed = [E('n1', 'n2'), E('n2', 'n3'), E('n3', 'n4'), E('n4', 'n5'), E('n5', 'n6'), E('n6', 'n7'),
    E('n7', 'a1', 'атакуют'), E('n7', 'b1', 'говорят'), E('n7', 'c1', 'уходят'),
    E('a1', 'a2'), E('a2', 'a3'), E('a3', 'a4', 'победили'), E('a3', 'a5', 'проиграли'),
    E('b1', 'b2'), E('b2', 'b3', 'без срыва'), E('b2', 'a1', 'срыв'), E('b3', 'b4'), E('b4', 'b5'), E('b5', 'b6'),
    E('c1', 'c2')];
  return { items: it, edges: ed };
}

// ================= Запуск =================
(async function init() {
  try { await DB.open(); } catch { DB.db = null; toast('Хранилище браузера недоступно — изменения не сохранятся после закрытия вкладки', 6000); setSaveState('Не сохраняется!', 'err'); }
  try { if (navigator.storage && navigator.storage.persist) navigator.storage.persist(); } catch {}
  ws = await DB.get('meta', 'ws');
  if (!ws) {
    const folder = { id: uid(), name: 'Партия 1 — Ведьма Акри', parent: null, open: true };
    const bId = uid(), s = sampleBoard();
    ws = { id: 'ws', folders: [folder], boards: [{ id: bId, name: 'Сценарий', folder: folder.id, updated: Date.now() }], current: bId };
    await DB.put('boards', { id: bId, items: s.items, edges: s.edges, view: null });
    await saveWs();
  }
  const start = ws.boards.find(b => b.id === ws.current) ? ws.current : ws.boards[0]?.id;
  if (start) await openBoard(start); else await newBoard(null, 'Новая доска');
  if (!MOBILE && innerWidth > 1200) toggleSidebar(true);
  // Кэш приложения не используется: снимаем старый service worker и его кэш, если остались от прошлых версий.
  try { navigator.serviceWorker?.getRegistrations().then(rs => rs.forEach(r => r.unregister())).catch(() => {}); } catch {}
  try { window.caches?.keys().then(ks => ks.forEach(k => caches.delete(k))).catch(() => {}); } catch {}
})();

window.__razvilka = { items, edges, view, selected, fit, estH }; // для отладки
})();
