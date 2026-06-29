/* Brute-force reachability checker — validates the math note and the curated
   levels. Run: node test/verify.js
   MODEL: the false split fires everywhere — a ball of value c_i ALWAYS splits
   to {a_i,b_i} (no normal split of c_i); the false pair {a_i,b_i} merges to c_i;
   every other value splits by halving and every other pair merges to its sum.
   Directed BFS over ball-multiset states, bounded by sum and ball count. */
'use strict';

function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { [a, b] = [b, a % b]; } return a; }
function stats(fs) {
  let H = 0, g = 0;
  for (const f of fs) { H = Math.max(H, f.a + f.b, f.c); g = gcd(g, Math.abs(f.a + f.b - f.c)); }
  return { H, M: H + 1, g: g || 1 };
}
function splitValue(v, fs) {
  for (const f of fs) if (f.c === v) return [f.a, f.b];   // false split overrides
  if (v <= 1) return null;
  return [Math.floor(v / 2), Math.ceil(v / 2)];
}
function mergeValue(x, y, fs) {
  for (const f of fs) if ((f.a === x && f.b === y) || (f.a === y && f.b === x)) return f.c;
  return x + y;
}
const key = a => a.slice().sort((p, q) => p - q).join(',');

function reach(s, t, fs, lenCap) {
  const st = stats(fs);
  const sumCap = Math.max(s, t) + st.H + 4;
  if (s === t) return true;
  const seen = new Set([key([s])]);
  let fr = [[s]];
  const goal = key([t]);
  while (fr.length) {
    const nx = [];
    for (const cur of fr) {
      for (let i = 0; i < cur.length; i++) {
        const k = splitValue(cur[i], fs);
        if (k) { const ns = cur.slice(); ns.splice(i, 1, k[0], k[1]); push(ns); }
      }
      for (let i = 0; i < cur.length; i++)
        for (let j = i + 1; j < cur.length; j++) {
          const v = mergeValue(cur[i], cur[j], fs);
          const ns = cur.filter((_, z) => z !== i && z !== j); ns.push(v); push(ns);
        }
    }
    fr = nx;
    function push(ns) {
      if (ns.length > lenCap) return;
      let sum = 0; for (const x of ns) sum += x;
      if (sum > sumCap) return;
      const kk = key(ns);
      if (seen.has(kk)) return;
      seen.add(kk); nx.push(ns);
    }
  }
  return seen.has(goal);
}

const CLASSIC = [{ a: 9, b: 10, c: 21 }];
const ADVANCED = [{ a: 2, b: 5, c: 3 }, { a: 1, b: 10, c: 2 }];

const LEVELS = {
  classic: [[19, 21], [21, 19], [24, 30], [30, 20], [22, 34], [23, 33]],
  advanced: [[12, 13], [14, 17], [15, 22], [24, 16], [18, 25], [13, 28]],
};

console.log('Classic stats:', stats(CLASSIC), '  Advanced stats:', stats(ADVANCED));
let ok = true;
for (const [mode, fs] of [['classic', CLASSIC], ['advanced', ADVANCED]]) {
  for (const [s, t] of LEVELS[mode]) {
    const r = reach(s, t, fs, 8);
    if (!r) ok = false;
    console.log(`  ${mode}: ${s} -> ${t} : ${r ? 'SOLVABLE ✓' : 'NOT FOUND ✗'}`);
  }
}

console.log('\nSharpness (Classic, H=21, so M=22):');
const sharp = [
  ['21 -> 23 (the trap, want UNSOLVABLE)', 21, 23, false],
  ['23 -> 21 (one-way door, want solvable)', 23, 21, true],
  ['22 -> 34 (>=M, want solvable)', 22, 34, true],
];
for (const [lbl, s, t, exp] of sharp) {
  const r = reach(s, t, CLASSIC, 8);
  const pass = r === exp; ok = ok && pass;
  console.log(`  ${lbl}: ${r ? 'reachable' : 'unreachable'}  ${pass ? 'OK' : 'UNEXPECTED'}`);
}
process.exit(ok ? 0 : 1);
