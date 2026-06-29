/* Brute-force reachability checker — validates the math note and the rulesets.
   Run: node test/verify.js
   MODEL: the false split fires everywhere — a ball of value c_i ALWAYS splits
   to {a_i,b_i}; the false pair {a_i,b_i} merges to c_i; every other value halves
   and every other pair sums.
   Directed BFS over ball-multiset states, bounded by sum and ball count. The
   bound makes large g=1 targets infeasible to confirm exhaustively here — those
   are covered by the theorem (both endpoints >= M, congruent mod g => solvable).
*/
'use strict';

function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { [a, b] = [b, a % b]; } return a; }
function stats(fs) {
  let H = 0, g = 0;
  for (const f of fs) { H = Math.max(H, f.a + f.b, f.c); g = gcd(g, Math.abs(f.a + f.b - f.c)); }
  return { H, M: H + 1, g: g || 1 };
}
function splitValue(v, fs) {
  for (const f of fs) if (f.c === v) return [f.a, f.b];
  if (v <= 1) return null;
  return [Math.floor(v / 2), Math.ceil(v / 2)];
}
function mergeValue(x, y, fs) {
  for (const f of fs) if ((f.a === x && f.b === y) || (f.a === y && f.b === x)) return f.c;
  return x + y;
}
const key = a => a.slice().sort((p, q) => p - q).join(',');

function reach(s, t, fs, lenCap, pad) {
  const st = stats(fs);
  const sumCap = Math.max(s, t) + st.H + (pad == null ? 4 : pad);
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
const ADVANCED = [{ a: 9, b: 10, c: 21 }, { a: 2, b: 5, c: 3 }, { a: 1, b: 10, c: 2 }];

console.log('Classic :', stats(CLASSIC));
console.log('Advanced:', stats(ADVANCED));
let ok = true;
const T = (cond, label) => { ok = ok && cond; console.log(`  [${cond ? 'OK ' : 'FAIL'}] ${label}`); };

// --- Classic: sufficiency spot-checks above M, plus sharpness --------------
console.log('\nClassic (M=22, g=2):');
let suffOK = true;
for (const [s, t] of [[22, 24], [24, 22], [22, 34], [23, 33], [33, 23], [30, 22]])
  if (!reach(s, t, CLASSIC, 8)) { suffOK = false; console.log(`     missed ${s}->${t}`); }
T(suffOK, 'sampled same-parity pairs >= M are solvable (sufficiency)');
T(reach(19, 21, CLASSIC, 8), 'iconic 19 -> 21 solvable');
T(reach(23, 21, CLASSIC, 8), '23 -> 21 solvable (one-way door, easy side)');
T(!reach(21, 23, CLASSIC, 8), '21 -> 23 UNSOLVABLE (the 21-trap => M=22 is sharp)');

// --- Advanced: small-delta spot checks (large g=1 targets => theorem) -------
console.log('\nAdvanced (M=22, g=1):');
// (g=1 + tiny magic numbers => the bounded BFS explodes; the theorem covers
//  all s,t >= M, so we only spot-check a couple of fast upward cases here)
for (const [s, t] of [[22, 23], [22, 24]])
  T(reach(s, t, ADVANCED, 9, 5), `${s} -> ${t} solvable`);

process.exit(ok ? 0 : 1);
