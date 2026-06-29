/* ===========================================================================
   Ya Stupid — a tiny physics game about (deliberately) bad arithmetic.
   9 + 10 = 21.  Vanilla JS, no dependencies.
   =========================================================================== */
'use strict';

/* ----------------------------- rulesets ---------------------------------- */
// A false sum: the pair {a,b} merges to c, and any ball of value c splits to {a,b}.
const RULESETS = {
  classic: {
    name: 'Classic',
    falseSums: [{ a: 9, b: 10, c: 21 }],
  },
  advanced: {
    name: 'Advanced',
    falseSums: [{ a: 9, b: 10, c: 21 }, { a: 2, b: 5, c: 3 }, { a: 1, b: 10, c: 2 }],
  },
};

/* ------------------------- arithmetic of the lie -------------------------- */
function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { [a, b] = [b, a % b]; } return a; }

function rulesetStats(fs) {
  let H = 0, g = 0;
  for (const f of fs) { H = Math.max(H, f.a + f.b, f.c); g = gcd(g, Math.abs((f.a + f.b) - f.c)); }
  return { H, M: H + 1, g: g || 1 };
}
function splitValue(v, fs) {
  for (const f of fs) if (f.c === v) return [f.a, f.b];   // false split overrides
  if (v <= 1) return null;                                // a 1 cannot be split
  return [Math.floor(v / 2), Math.ceil(v / 2)];
}
function mergeValue(x, y, fs) {
  for (const f of fs) if ((f.a === x && f.b === y) || (f.a === y && f.b === x)) return f.c;
  return x + y;
}
function isFalseRHS(v, fs) { return fs.some(f => f.c === v); }

// A random puzzle: both endpoints in [M, 99] and congruent mod g  => provably
// solvable (see docs/minimum-value.md).
function randInt(lo, hi) { return lo + Math.floor(Math.random() * (hi - lo + 1)); }
function generateLevel(fs) {
  const st = rulesetStats(fs);
  const lo = st.M, hi = 99;
  const maxSteps = Math.floor((hi - lo) / st.g);
  const s = randInt(lo, hi - ((hi - lo) % st.g));          // s in range, on the lattice from lo
  // choose a non-zero step count, prefer a few hops for flavour
  let steps = randInt(1, Math.max(1, Math.min(maxSteps, 16)));
  let dir = Math.random() < 0.5 ? -1 : 1;
  let t = s + dir * steps * st.g;
  if (t < lo || t > hi) t = s - dir * steps * st.g;
  if (t < lo || t > hi || t === s) t = (s + st.g <= hi) ? s + st.g : s - st.g;
  return { s, t };
}

/* ------------------------------ visuals ----------------------------------- */
function valueHue(v) { return (v * 47) % 360; }
function radiusFor(v) { return Math.min(74, 17 + 6 * Math.sqrt(v)); }

/* ------------------------------- state ------------------------------------ */
const canvas = document.getElementById('board');
const ctx = canvas.getContext('2d');
let W = 0, VH = 0, DPR = 1;
function resize() {
  DPR = Math.min(window.devicePixelRatio || 1, 2.5);
  W = window.innerWidth; VH = window.innerHeight;
  canvas.width = Math.round(W * DPR); canvas.height = Math.round(VH * DPR);
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
}
window.addEventListener('resize', resize);
resize();

let nextId = 1;
let balls = [];
let beams = [];
let config = null;        // {fs, stats, s, t, mode}
let moves = 0;
let won = false;
let tNow = 0;

function makeBall(value, x, y, vx = 0, vy = 0) {
  return { id: nextId++, value, x, y, vx, vy, r: radiusFor(value), pulse: 1 };
}
function ballById(id) { return balls.find(b => b.id === id); }

let mode = localStorage.getItem('yastupid_mode') || 'classic';

function startLevel(s, t) {
  const fs = RULESETS[mode].falseSums;
  const stats = rulesetStats(fs);
  config = { fs, stats, s, t, mode };
  balls = []; beams = []; moves = 0; won = false; nextId = 1;
  balls.push(makeBall(s, W / 2, VH * 0.45));
  updateHud();
  hideMenu(); hide('win');
}
function newRandomLevel() {
  const { s, t } = generateLevel(RULESETS[mode].falseSums);
  startLevel(s, t);
}

/* ------------------------------- physics ---------------------------------- */
const REPULSE = 1400, BEAM_PULL = 22, DAMP = 0.86, BOUNCE = 0.5;

function step(dt) {
  const pad = 6;
  for (let i = 0; i < balls.length; i++)
    for (let j = i + 1; j < balls.length; j++) {
      const A = balls[i], B = balls[j];
      let dx = B.x - A.x, dy = B.y - A.y, d = Math.hypot(dx, dy) || 0.001;
      const min = A.r + B.r + 4;
      if (d < min && !isBeamed(A.id, B.id)) {
        const push = (REPULSE / (d * d)) * (min - d) * dt, nx = dx / d, ny = dy / d;
        A.vx -= nx * push; A.vy -= ny * push; B.vx += nx * push; B.vy += ny * push;
      }
    }
  for (const beam of beams) {
    const A = ballById(beam.a), B = ballById(beam.b); if (!A || !B) continue;
    let dx = B.x - A.x, dy = B.y - A.y, d = Math.hypot(dx, dy) || 0.001;
    const nx = dx / d, ny = dy / d, f = BEAM_PULL * dt;
    A.vx += nx * f; A.vy += ny * f; B.vx -= nx * f; B.vy -= ny * f;
  }
  for (const b of balls) {
    b.vx *= DAMP; b.vy *= DAMP;
    const sp = Math.hypot(b.vx, b.vy); if (sp > 900) { b.vx *= 900 / sp; b.vy *= 900 / sp; }
    b.x += b.vx * dt; b.y += b.vy * dt;
    if (b.x < b.r + pad) { b.x = b.r + pad; b.vx = Math.abs(b.vx) * BOUNCE; }
    if (b.x > W - b.r - pad) { b.x = W - b.r - pad; b.vx = -Math.abs(b.vx) * BOUNCE; }
    const top = b.r + pad + 72, bot = VH - b.r - pad - 56;
    if (b.y < top) { b.y = top; b.vy = Math.abs(b.vy) * BOUNCE; }
    if (b.y > bot) { b.y = bot; b.vy = -Math.abs(b.vy) * BOUNCE; }
    if (b.pulse > 1) b.pulse = Math.max(1, b.pulse - dt * 3);
  }
  for (const beam of beams.slice()) {
    const A = ballById(beam.a), B = ballById(beam.b);
    if (!A || !B) { beams = beams.filter(x => x !== beam); continue; }
    if (Math.hypot(B.x - A.x, B.y - A.y) <= A.r + B.r - 2) fuse(A, B);
  }
}

/* ------------------------------ operations -------------------------------- */
function split(ball) {
  if (won) return;
  const kids = splitValue(ball.value, config.fs);
  if (!kids) { ball.pulse = 1.6; ball.vx += (Math.random() - .5) * 80; toast("A 1 can't split!"); return; }
  const idx = balls.indexOf(ball); if (idx >= 0) balls.splice(idx, 1);
  const ang = Math.random() * Math.PI * 2;
  for (let k = 0; k < kids.length; k++) {
    const a = ang + (k ? Math.PI : 0);
    const nb = makeBall(kids[k], ball.x + Math.cos(a) * 14, ball.y + Math.sin(a) * 14,
      Math.cos(a) * 170, Math.sin(a) * 170);
    nb.pulse = 1.5; balls.push(nb);
  }
  moves++; afterChange();
}
function fuse(A, B) {
  const value = mergeValue(A.value, B.value, config.fs);
  const x = (A.x + B.x) / 2, y = (A.y + B.y) / 2;
  balls = balls.filter(b => b !== A && b !== B);
  beams = beams.filter(bm => ![A.id, B.id].includes(bm.a) && ![A.id, B.id].includes(bm.b));
  const nb = makeBall(value, x, y, (A.vx + B.vx) / 2, (A.vy + B.vy) / 2);
  nb.pulse = 1.7; balls.push(nb);
  moves++; afterChange();
}
function afterChange() {
  updateHud();
  if (balls.length === 1 && balls[0].value === config.t && !won) { won = true; setTimeout(showWin, 480); }
}

/* --------------------------------- beams ---------------------------------- */
function isBeamed(a, b) { return beams.some(x => (x.a === a && x.b === b) || (x.a === b && x.b === a)); }
function addBeam(a, b) {
  if (a === b || isBeamed(a, b)) return;
  beams.push({ a, b });
  const A = ballById(a), B = ballById(b); if (A) A.pulse = 1.4; if (B) B.pulse = 1.4;
}

/* ------------------------------- rendering -------------------------------- */
function draw() {
  ctx.clearRect(0, 0, W, VH);
  for (const beam of beams) drawBeam(ballById(beam.a), ballById(beam.b), false);
  if (drag && drag.moved) {
    const A = ballById(drag.id);
    if (A) drawBeam(A, { x: drag.x, y: drag.y, value: A.value }, true);
  }
  for (const b of balls) drawBall(b);
}

function drawBeam(A, B, aiming) {
  if (!A || !B) return;
  const dx = B.x - A.x, dy = B.y - A.y, len = Math.hypot(dx, dy) || 0.001;
  const nx = dx / len, ny = dy / len, px = -ny, py = nx;
  const wob = Math.sin(tNow * 9) * Math.min(13, len * 0.07);
  const cx = (A.x + B.x) / 2 + px * wob, cy = (A.y + B.y) / 2 + py * wob;
  const grad = ctx.createLinearGradient(A.x, A.y, B.x, B.y);
  grad.addColorStop(0, `hsl(${valueHue(A.value)},85%,60%)`);
  grad.addColorStop(1, `hsl(${valueHue(B.value)},85%,60%)`);
  ctx.save(); ctx.lineCap = 'round';
  // soft coloured band
  ctx.globalAlpha = aiming ? .35 : .55; ctx.strokeStyle = grad; ctx.lineWidth = aiming ? 7 : 10;
  ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.quadraticCurveTo(cx, cy, B.x, B.y); ctx.stroke();
  // bright core (a touch of additive sparkle, but restrained)
  ctx.globalCompositeOperation = 'lighter'; ctx.globalAlpha = 1;
  ctx.strokeStyle = 'rgba(255,250,235,.95)'; ctx.lineWidth = aiming ? 2 : 3;
  ctx.beginPath(); ctx.moveTo(A.x, A.y); ctx.quadraticCurveTo(cx, cy, B.x, B.y); ctx.stroke();
  if (!aiming) {                                  // travelling energy beads
    const beads = Math.max(2, Math.floor(len / 30));
    for (let i = 0; i < beads; i++) {
      const p = ((i / beads) + tNow * 0.7) % 1, mt = 1 - p;
      const x = mt * mt * A.x + 2 * mt * p * cx + p * p * B.x;
      const y = mt * mt * A.y + 2 * mt * p * cy + p * p * B.y;
      ctx.fillStyle = '#fffbe9'; ctx.beginPath(); ctx.arc(x, y, 2.6, 0, 7); ctx.fill();
    }
  }
  ctx.restore();
}

function drawBall(b) {
  const hue = valueHue(b.value), r = b.r * b.pulse;
  // glossy body with a real drop shadow (not a neon glow)
  ctx.save();
  ctx.shadowColor = 'rgba(40,28,6,.40)'; ctx.shadowBlur = 9; ctx.shadowOffsetY = 5;
  const g = ctx.createRadialGradient(b.x - r * .34, b.y - r * .4, r * .12, b.x, b.y, r);
  g.addColorStop(0, `hsl(${hue},92%,84%)`);
  g.addColorStop(.5, `hsl(${hue},78%,60%)`);
  g.addColorStop(1, `hsl(${hue},66%,42%)`);
  ctx.beginPath(); ctx.arc(b.x, b.y, r, 0, 7); ctx.fillStyle = g; ctx.fill();
  ctx.restore();
  // dark rim
  ctx.lineWidth = Math.max(2, r * .07); ctx.strokeStyle = `hsl(${hue},55%,28%)`;
  ctx.beginPath(); ctx.arc(b.x, b.y, r - ctx.lineWidth / 2, 0, 7); ctx.stroke();
  // dashed marker on the "magic" numbers
  if (config && isFalseRHS(b.value, config.fs)) {
    ctx.save(); ctx.setLineDash([4, 5]); ctx.lineWidth = 2;
    ctx.strokeStyle = 'rgba(255,255,255,.85)';
    ctx.beginPath(); ctx.arc(b.x, b.y, r - r * .22, 0, 7); ctx.stroke(); ctx.restore();
  }
  // specular highlight
  ctx.beginPath(); ctx.ellipse(b.x - r * .33, b.y - r * .4, r * .3, r * .18, -0.5, 0, 7);
  ctx.fillStyle = 'rgba(255,255,255,.55)'; ctx.fill();
  // number
  ctx.font = `900 ${Math.max(14, r * .82)}px ui-rounded,"Trebuchet MS",system-ui,sans-serif`;
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  ctx.lineWidth = 3.5; ctx.strokeStyle = 'rgba(255,255,255,.65)';
  ctx.strokeText(String(b.value), b.x, b.y + 1);
  ctx.fillStyle = '#22150a'; ctx.fillText(String(b.value), b.x, b.y + 1);
}

/* --------------------------------- loop ----------------------------------- */
let lastT = performance.now();
requestAnimationFrame(function frame(now) {
  let dt = Math.min((now - lastT) / 1000, 0.033); lastT = now; tNow += dt;
  if (config) { step(dt); draw(); }
  requestAnimationFrame(frame);
});

/* --------------------------------- input ---------------------------------- */
let drag = null;
const TAP_MOVE = 14;
function pos(e) { const r = canvas.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top }; }
function pointAt(x, y) {
  for (let i = balls.length - 1; i >= 0; i--) {
    const b = balls[i]; if (Math.hypot(x - b.x, y - b.y) <= b.r + 8) return b;
  }
  return null;
}
canvas.addEventListener('pointerdown', e => {
  if (!config || won) return;
  const { x, y } = pos(e); const b = pointAt(x, y); if (!b) return;
  drag = { id: b.id, sx: x, sy: y, x, y, moved: false };
  try { canvas.setPointerCapture(e.pointerId); } catch (_) {}
  e.preventDefault();
});
canvas.addEventListener('pointermove', e => {
  if (!drag) return;
  const { x, y } = pos(e); drag.x = x; drag.y = y;
  if (Math.hypot(x - drag.sx, y - drag.sy) > TAP_MOVE) drag.moved = true;
  e.preventDefault();
});
canvas.addEventListener('pointerup', e => {
  if (!drag) return;
  const { x, y } = pos(e), src = ballById(drag.id), tgt = pointAt(x, y);
  if (src) {
    if (drag.moved && tgt && tgt.id !== src.id) addBeam(src.id, tgt.id);   // drag → fuse
    else if (!drag.moved) split(src);                                      // tap → split
  }
  drag = null; e.preventDefault();
});
canvas.addEventListener('pointercancel', () => { drag = null; });

/* --------------------------------- HUD ------------------------------------ */
const el = id => document.getElementById(id);
function updateHud() {
  el('targetVal').textContent = config ? config.t : '—';
  el('moveVal').textContent = moves;
  el('sumVal').textContent = balls.reduce((s, b) => s + b.value, 0);
}
let toastTimer = null;
function toast(msg) {
  const t = el('toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), 1800);
}

/* ------------------------------- popovers --------------------------------- */
function show(id) { el(id).classList.remove('hidden'); }
function hide(id) { el(id).classList.add('hidden'); }

function openMenu() {
  document.querySelectorAll('.seg-btn').forEach(b => b.classList.toggle('active', b.dataset.mode === mode));
  const st = rulesetStats(RULESETS[mode].falseSums);
  el('ruleLine').innerHTML = mode === 'classic'
    ? `Classic: one lie. Targets share parity and sit in <b>[${st.M}, 99]</b>.`
    : `Advanced: three lies (incl. 9+10=21). Step <b>g = ${st.g}</b>, range <b>[${st.M}, 99]</b>.`;
  show('menu');
}
function hideMenu() { hide('menu'); }

function showWin() {
  el('winLine').textContent = `${config.s} → ${config.t} in ${moves} move${moves === 1 ? '' : 's'}.`;
  el('burst').textContent = ['⭐', '🎉', '🏆', '💥', '🎯'][moves % 5];
  show('win');
}

/* ------------------------------ UI wiring --------------------------------- */
el('menuBtn').onclick = openMenu;
el('closeMenu').onclick = hideMenu;
el('newBtn').onclick = newRandomLevel;
el('newMenuBtn').onclick = newRandomLevel;
el('againBtn').onclick = newRandomLevel;
el('restartBtn').onclick = () => startLevel(config.s, config.t);
document.querySelectorAll('.seg-btn').forEach(btn => {
  btn.onclick = () => {
    if (mode === btn.dataset.mode) { hideMenu(); return; }
    mode = btn.dataset.mode; localStorage.setItem('yastupid_mode', mode);
    newRandomLevel();
  };
});

/* ------------------------------- boot ------------------------------------- */
newRandomLevel();          // jump straight into a random puzzle — no landing screen
