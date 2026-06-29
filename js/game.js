/* ===========================================================================
   Ya Stupid — a tiny physics game about (deliberately) bad arithmetic.
   Vanilla JS, no dependencies. 9 + 10 = 21.
   =========================================================================== */
'use strict';

/* ----------------------------- rulesets ---------------------------------- */
// A false sum: the pair {a,b} merges to c, and any ball of value c splits to {a,b}.
const RULESETS = {
  classic: {
    name: 'Classic',
    blurb: 'One glorious lie: 9 + 10 = 21.',
    falseSums: [{ a: 9, b: 10, c: 21 }],
  },
  advanced: {
    name: 'Advanced',
    blurb: 'Two lies: 2 + 5 = 3 and 10 + 1 = 2.',
    falseSums: [{ a: 2, b: 5, c: 3 }, { a: 1, b: 10, c: 2 }],
  },
};

const LEVELS = {
  classic: [
    { name: 'The Meme', s: 19, t: 21 },
    { name: 'Undo It',  s: 21, t: 19 },
    { name: 'Climb',    s: 24, t: 30 },
    { name: 'Descend',  s: 30, t: 20 },
    { name: 'Stretch',  s: 22, t: 34 },
    { name: 'Odd One',  s: 23, t: 33 },
  ],
  advanced: [
    { name: 'Plus One', s: 12, t: 13 },
    { name: 'Tiny Gap', s: 14, t: 17 },
    { name: 'Upward',   s: 15, t: 22 },
    { name: 'Down',     s: 24, t: 16 },
    { name: 'Mix',      s: 18, t: 25 },
    { name: 'Long Way', s: 13, t: 28 },
  ],
};

/* ------------------------- arithmetic of the lie -------------------------- */
function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { [a, b] = [b, a % b]; } return a; }

function rulesetStats(fs) {
  let H = 0, g = 0;
  for (const f of fs) {
    H = Math.max(H, f.a + f.b, f.c);
    g = gcd(g, Math.abs((f.a + f.b) - f.c));
  }
  return { H, M: H + 1, g: g || 1 };
}

// Split a value into its two children (false split overrides normal split).
function splitValue(v, fs) {
  for (const f of fs) if (f.c === v) return [f.a, f.b];
  if (v <= 1) return null;                 // a 1 cannot be split
  return [Math.floor(v / 2), Math.ceil(v / 2)];
}

// Merge two values (false merge overrides normal merge).
function mergeValue(x, y, fs) {
  for (const f of fs) {
    if ((f.a === x && f.b === y) || (f.a === y && f.b === x)) return f.c;
  }
  return x + y;
}

function isGuaranteed(s, t, stats) {
  return s >= stats.M && t >= stats.M && (t - s) % stats.g === 0;
}

/* ------------------------------ visuals ----------------------------------- */
function valueHue(v) { return (v * 47) % 360; }      // stable colour per value
function radiusFor(v) { return 20 + 7 * Math.sqrt(v); }

/* ------------------------------- state ------------------------------------ */
const canvas = document.getElementById('board');
const ctx = canvas.getContext('2d');

let W = 0, H = 0, DPR = 1;
function resize() {
  DPR = Math.min(window.devicePixelRatio || 1, 2.5);
  W = window.innerWidth; H = window.innerHeight;
  canvas.width = Math.round(W * DPR);
  canvas.height = Math.round(H * DPR);
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
}
window.addEventListener('resize', resize);
resize();

let nextId = 1;
let balls = [];
let beams = [];           // {a:id, b:id} pending fusions
let config = null;        // {fs, stats, s, t, mode, levelIndex}
let moves = 0;
let won = false;
let tNow = 0;

function makeBall(value, x, y, vx = 0, vy = 0) {
  return { id: nextId++, value, x, y, vx, vy, r: radiusFor(value), born: tNow, pulse: 1 };
}
function ballById(id) { return balls.find(b => b.id === id); }

/* ------------------------------ level setup ------------------------------- */
const solved = JSON.parse(localStorage.getItem('yastupid_solved') || '{}');
function markSolved(mode, i) {
  solved[mode + ':' + i] = true;
  localStorage.setItem('yastupid_solved', JSON.stringify(solved));
}

function startLevel(mode, levelIndex, s, t) {
  const fs = RULESETS[mode].falseSums;
  const stats = rulesetStats(fs);
  config = { fs, stats, s, t, mode, levelIndex };
  balls = [];
  beams = [];
  moves = 0;
  won = false;
  nextId = 1;
  balls.push(makeBall(s, W / 2, H * 0.42));
  updateHud();
  hideOverlay('menu');
  hideOverlay('win');
  showHint('Tap a ball to split · Drag between balls to fuse');
}

/* ------------------------------- physics ---------------------------------- */
const REPULSE = 1400;     // soft separation strength
const BEAM_PULL = 22;     // attraction along an active beam
const DAMP = 0.86;        // velocity damping per step
const WALL_BOUNCE = 0.5;

function step(dt) {
  const pad = 6;
  // pairwise soft repulsion (keeps balls from stacking)
  for (let i = 0; i < balls.length; i++) {
    for (let j = i + 1; j < balls.length; j++) {
      const A = balls[i], B = balls[j];
      let dx = B.x - A.x, dy = B.y - A.y;
      let d = Math.hypot(dx, dy) || 0.001;
      const min = A.r + B.r + 4;
      const beamed = isBeamed(A.id, B.id);
      if (d < min && !beamed) {
        const push = (REPULSE / (d * d)) * (min - d) * dt;
        const nx = dx / d, ny = dy / d;
        A.vx -= nx * push; A.vy -= ny * push;
        B.vx += nx * push; B.vy += ny * push;
      }
    }
  }

  // beam attraction
  for (const beam of beams) {
    const A = ballById(beam.a), B = ballById(beam.b);
    if (!A || !B) continue;
    let dx = B.x - A.x, dy = B.y - A.y;
    let d = Math.hypot(dx, dy) || 0.001;
    const nx = dx / d, ny = dy / d;
    const f = BEAM_PULL * dt;
    A.vx += nx * f; A.vy += ny * f;
    B.vx -= nx * f; B.vy -= ny * f;
  }

  // integrate + walls
  for (const b of balls) {
    b.vx *= DAMP; b.vy *= DAMP;
    const sp = Math.hypot(b.vx, b.vy);
    const cap = 900;
    if (sp > cap) { b.vx *= cap / sp; b.vy *= cap / sp; }
    b.x += b.vx * dt; b.y += b.vy * dt;
    if (b.x < b.r + pad) { b.x = b.r + pad; b.vx = Math.abs(b.vx) * WALL_BOUNCE; }
    if (b.x > W - b.r - pad) { b.x = W - b.r - pad; b.vx = -Math.abs(b.vx) * WALL_BOUNCE; }
    const topY = b.r + pad + 70, botY = H - b.r - pad - 70;
    if (b.y < topY) { b.y = topY; b.vy = Math.abs(b.vy) * WALL_BOUNCE; }
    if (b.y > botY) { b.y = botY; b.vy = -Math.abs(b.vy) * WALL_BOUNCE; }
    if (b.pulse > 1) b.pulse = Math.max(1, b.pulse - dt * 3);
  }

  // resolve beam contacts -> fuse
  for (const beam of beams.slice()) {
    const A = ballById(beam.a), B = ballById(beam.b);
    if (!A || !B) { beams = beams.filter(x => x !== beam); continue; }
    const d = Math.hypot(B.x - A.x, B.y - A.y);
    if (d <= A.r + B.r - 2) fuse(A, B);
  }
}

/* ------------------------------ operations -------------------------------- */
function split(ball) {
  if (won) return;
  const kids = splitValue(ball.value, config.fs);
  if (!kids) { ball.pulse = 1.6; ball.vx += (Math.random() - .5) * 60; return; } // 1 can't split: jiggle
  const idx = balls.indexOf(ball);
  if (idx >= 0) balls.splice(idx, 1);
  const ang = Math.random() * Math.PI * 2;
  for (let k = 0; k < kids.length; k++) {
    const a = ang + (k ? Math.PI : 0);
    const nb = makeBall(kids[k], ball.x + Math.cos(a) * 14, ball.y + Math.sin(a) * 14,
      Math.cos(a) * 160, Math.sin(a) * 160);
    nb.pulse = 1.5;
    balls.push(nb);
  }
  moves++;
  afterChange();
}

function fuse(A, B) {
  const value = mergeValue(A.value, B.value, config.fs);
  const x = (A.x + B.x) / 2, y = (A.y + B.y) / 2;
  const vx = (A.vx + B.vx) / 2, vy = (A.vy + B.vy) / 2;
  balls = balls.filter(b => b !== A && b !== B);
  beams = beams.filter(bm => bm.a !== A.id && bm.b !== A.id && bm.a !== B.id && bm.b !== B.id);
  const nb = makeBall(value, x, y, vx, vy);
  nb.pulse = 1.7;
  balls.push(nb);
  moves++;
  afterChange();
}

function afterChange() {
  updateHud();
  if (balls.length === 1 && balls[0].value === config.t && !won) {
    won = true;
    setTimeout(showWin, 450);
  }
}

/* --------------------------------- beams ---------------------------------- */
function isBeamed(id1, id2) {
  return beams.some(b => (b.a === id1 && b.b === id2) || (b.a === id2 && b.b === id1));
}
function addBeam(id1, id2) {
  if (id1 === id2 || isBeamed(id1, id2)) return;
  beams.push({ a: id1, b: id2 });
  const A = ballById(id1), B = ballById(id2);
  if (A) A.pulse = 1.4; if (B) B.pulse = 1.4;
}

/* ------------------------------- rendering -------------------------------- */
function draw() {
  ctx.clearRect(0, 0, W, H);

  // active beams (proton beam look)
  for (const beam of beams) drawBeam(ballById(beam.a), ballById(beam.b), false);
  // beam being aimed by finger
  if (drag && drag.from && drag.moved) {
    const A = ballById(drag.from);
    if (A) drawBeam(A, { x: drag.x, y: drag.y, value: A.value }, true);
  }

  for (const b of balls) drawBall(b);
}

function drawBeam(A, B, aiming) {
  if (!A || !B) return;
  const dx = B.x - A.x, dy = B.y - A.y;
  const len = Math.hypot(dx, dy) || 0.001;
  const nx = dx / len, ny = dy / len;
  const h1 = valueHue(A.value), h2 = valueHue(B.value);
  const grad = ctx.createLinearGradient(A.x, A.y, B.x, B.y);
  grad.addColorStop(0, `hsla(${h1},90%,70%,${aiming ? .5 : .9})`);
  grad.addColorStop(1, `hsla(${h2},90%,70%,${aiming ? .5 : .9})`);

  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  // soft outer glow
  ctx.strokeStyle = grad;
  ctx.lineCap = 'round';
  ctx.lineWidth = 12; ctx.globalAlpha = aiming ? .12 : .22;
  ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.lineTo(B.x, B.y); ctx.stroke();
  // bright core
  ctx.globalAlpha = 1; ctx.lineWidth = aiming ? 2 : 3.5;
  ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.lineTo(B.x, B.y); ctx.stroke();
  // travelling energy beads
  if (!aiming) {
    const beads = Math.max(2, Math.floor(len / 26));
    for (let i = 0; i < beads; i++) {
      let p = ((i / beads) + (tNow * 0.6)) % 1;
      const x = A.x + nx * len * p, y = A.y + ny * len * p;
      ctx.globalAlpha = .9;
      ctx.fillStyle = '#fff';
      ctx.beginPath(); ctx.arc(x, y, 2.4, 0, 7); ctx.fill();
    }
  }
  ctx.restore();
}

function drawBall(b) {
  const hue = valueHue(b.value);
  const r = b.r * b.pulse;
  ctx.save();
  // glow
  ctx.globalCompositeOperation = 'lighter';
  ctx.beginPath(); ctx.arc(b.x, b.y, r + 8, 0, 7);
  ctx.fillStyle = `hsla(${hue},90%,60%,.18)`; ctx.fill();
  ctx.restore();

  // body
  const g = ctx.createRadialGradient(b.x - r * .35, b.y - r * .4, r * .2, b.x, b.y, r);
  g.addColorStop(0, `hsl(${hue},95%,72%)`);
  g.addColorStop(1, `hsl(${hue},75%,42%)`);
  ctx.beginPath(); ctx.arc(b.x, b.y, r, 0, 7);
  ctx.fillStyle = g; ctx.fill();
  ctx.lineWidth = 2; ctx.strokeStyle = `hsla(${hue},95%,85%,.7)`; ctx.stroke();

  // value
  ctx.fillStyle = '#06101f';
  ctx.font = `800 ${Math.max(15, r * 0.78)}px -apple-system,Segoe UI,Roboto,sans-serif`;
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.fillText(String(b.value), b.x, b.y + 1);
  ctx.restore();
}

/* --------------------------------- loop ----------------------------------- */
let lastT = performance.now();
function frame(now) {
  let dt = (now - lastT) / 1000; lastT = now;
  dt = Math.min(dt, 0.033);
  tNow += dt;
  if (config) { step(dt); draw(); }
  requestAnimationFrame(frame);
}
requestAnimationFrame(frame);

/* --------------------------------- input ---------------------------------- */
let drag = null;   // {from:id, x, y, sx, sy, moved, t}
const TAP_MOVE = 12, TAP_TIME = 350;

function pointAt(x, y) {
  // topmost ball under point
  for (let i = balls.length - 1; i >= 0; i--) {
    const b = balls[i];
    if (Math.hypot(x - b.x, y - b.y) <= b.r + 6) return b;
  }
  return null;
}
function evtPos(e) {
  const r = canvas.getBoundingClientRect();
  const p = e.touches ? e.touches[0] : e;
  return { x: p.clientX - r.left, y: p.clientY - r.top };
}

function onDown(e) {
  if (won || !config) return;
  const { x, y } = evtPos(e);
  const b = pointAt(x, y);
  if (!b) return;
  drag = { from: b.id, x, y, sx: x, sy: y, moved: false, t: performance.now() };
  e.preventDefault();
}
function onMove(e) {
  if (!drag) return;
  const { x, y } = evtPos(e);
  drag.x = x; drag.y = y;
  if (Math.hypot(x - drag.sx, y - drag.sy) > TAP_MOVE) drag.moved = true;
  e.preventDefault();
}
function onUp(e) {
  if (!drag) return;
  const { x, y } = evtPos(e);
  const src = ballById(drag.from);
  const elapsed = performance.now() - drag.t;
  const target = pointAt(x, y);
  if (src) {
    if (!drag.moved && elapsed < TAP_TIME) {
      split(src);                       // tap
    } else if (target && target.id !== src.id) {
      addBeam(src.id, target.id);       // drag onto another ball
    }
  }
  drag = null;
  fadeHint();
  e.preventDefault();
}

canvas.addEventListener('mousedown', onDown);
window.addEventListener('mousemove', onMove);
window.addEventListener('mouseup', onUp);
canvas.addEventListener('touchstart', onDown, { passive: false });
window.addEventListener('touchmove', onMove, { passive: false });
window.addEventListener('touchend', onUp, { passive: false });

/* --------------------------------- HUD ------------------------------------ */
const el = id => document.getElementById(id);
function updateHud() {
  el('targetVal').textContent = config ? config.t : '—';
  el('ballCount').textContent = balls.length;
  el('sumVal').textContent = balls.reduce((s, b) => s + b.value, 0);
  el('moveVal').textContent = moves;
}
let hintTimer = null;
function showHint(txt) { const h = el('hint'); h.textContent = txt; h.style.opacity = '1'; }
function fadeHint() { clearTimeout(hintTimer); hintTimer = setTimeout(() => { el('hint').style.opacity = '0'; }, 2600); }

/* ------------------------------- overlays --------------------------------- */
function showOverlay(id) { el(id).classList.remove('hidden'); }
function hideOverlay(id) { el(id).classList.add('hidden'); }

function showWin() {
  const c = config;
  el('winLine').textContent = `${c.s} → ${c.t} in ${moves} move${moves === 1 ? '' : 's'}.`;
  if (c.levelIndex != null) markSolved(c.mode, c.levelIndex);
  showOverlay('win');
}

let menuMode = 'classic';
function renderMenu() {
  // ruleset line
  const fs = RULESETS[menuMode].falseSums;
  const stats = rulesetStats(fs);
  el('ruleLine').innerHTML =
    RULESETS[menuMode].blurb +
    `<br/>step g = ${stats.g} · guaranteed from M = ${stats.M}` +
    `<br/><em>Targets must differ from the start by a multiple of ${stats.g}.</em>`;

  // level grid
  const list = el('levelList');
  list.innerHTML = '';
  LEVELS[menuMode].forEach((lv, i) => {
    const btn = document.createElement('button');
    btn.className = 'lvl' + (solved[menuMode + ':' + i] ? ' solved' : '');
    btn.innerHTML = `<div class="lvl-name">${lv.name}</div>
      <div class="lvl-flow">${lv.s}<span class="arrow">→</span>${lv.t}</div>`;
    btn.onclick = () => startLevel(menuMode, i, lv.s, lv.t);
    list.appendChild(btn);
  });
  validateCustom();
}

function validateCustom() {
  const s = parseInt(el('customStart').value, 10);
  const t = parseInt(el('customTarget').value, 10);
  const stats = rulesetStats(RULESETS[menuMode].falseSums);
  const note = el('customNote');
  if (!Number.isFinite(s) || !Number.isFinite(t) || s < 1 || t < 1) {
    note.textContent = 'Enter two positive whole numbers.'; note.className = 'note bad'; return false;
  }
  if ((t - s) % stats.g !== 0) {
    note.textContent = `Impossible: must differ by a multiple of ${stats.g}.`;
    note.className = 'note bad'; return false;
  }
  if (isGuaranteed(s, t, stats)) {
    note.textContent = `Guaranteed solvable (both ≥ ${stats.M}).`; note.className = 'note ok'; return true;
  }
  note.textContent = `Below the guaranteed floor M = ${stats.M} — may still be solvable.`;
  note.className = 'note'; return true;
}

/* ------------------------------ UI wiring --------------------------------- */
el('menuBtn').onclick = () => { renderMenu(); showOverlay('menu'); };
el('resetBtn').onclick = () => { if (config) startLevel(config.mode, config.levelIndex, config.s, config.t); };
el('winMenuBtn').onclick = () => { renderMenu(); hideOverlay('win'); showOverlay('menu'); };
el('nextBtn').onclick = () => {
  const i = (config.levelIndex == null ? -1 : config.levelIndex) + 1;
  const list = LEVELS[config.mode];
  if (i < list.length) startLevel(config.mode, i, list[i].s, list[i].t);
  else { renderMenu(); hideOverlay('win'); showOverlay('menu'); }
};
el('playCustom').onclick = () => {
  if (!validateCustom()) return;
  const s = parseInt(el('customStart').value, 10);
  const t = parseInt(el('customTarget').value, 10);
  startLevel(menuMode, null, s, t);
};
el('customStart').oninput = validateCustom;
el('customTarget').oninput = validateCustom;

document.querySelectorAll('.seg-btn').forEach(btn => {
  btn.onclick = () => {
    document.querySelectorAll('.seg-btn').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    menuMode = btn.dataset.mode;
    renderMenu();
  };
});

/* ------------------------------- boot ------------------------------------- */
renderMenu();
showOverlay('menu');
