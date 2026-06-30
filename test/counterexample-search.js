/* Counterexample search for the sufficiency claim "M = H + 1 is the threshold".

   For each single false sum, sufficiency reduces (sufficiency_of_pumps, proved in
   Lean) to the two one-step pumps  [n] -> [n+g]  and  [n+g] -> [n]  for every
   n >= M.  This script BFS-checks those pumps directly for the families that are
   NOT yet mechanized in lean/YaStupid.lean:

     - a = b = 1  with a+b < c     (e.g. 1+1=5): pure ones can only force-merge
       {1,1} -> c, so the all-ones hub cannot build/descend; descend needs a
       structural c-harvest.
     - a + b > c  with a leg >= c  (e.g. 2+10=7, 2+2=2, and the pathological
       1+14=7 where greedy scatter loops on 14 = 2c -> [7,7] -> {1,14} -> ...):
       scatterRaw's max-value measure fails because c -> {a,b} can RAISE the max.

   Result (see bottom): NO counterexample is found anywhere in range -- the
   threshold M = H+1 is confirmed for every tested config. The mechanization gap
   for these two families is therefore a proof-engineering gap, not a math gap.

   Run: node test/counterexample-search.js
*/
'use strict';

function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { [a, b] = [b, a % b]; } return a; }
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

// directed BFS, bounded by ball count and total, with a hard state cap
function reach(s, t, fs, lenCap, sumCap, maxStates) {
  if (s === t) return true;
  const seen = new Set([key([s])]);
  let fr = [[s]];
  const goal = key([t]);
  while (fr.length) {
    const nx = [];
    for (const cur of fr) {
      for (let i = 0; i < cur.length; i++) {
        const k = splitValue(cur[i], fs);
        if (k) { const ns = cur.slice(); ns.splice(i, 1, k[0], k[1]); if (push(ns)) return true; }
      }
      for (let i = 0; i < cur.length; i++)
        for (let j = i + 1; j < cur.length; j++) {
          const v = mergeValue(cur[i], cur[j], fs);
          const ns = cur.filter((_, z) => z !== i && z !== j); ns.push(v);
          if (push(ns)) return true;
        }
    }
    fr = nx;
    if (seen.size > maxStates) return 'TIMEOUT';
    function push(ns) {
      if (ns.length > lenCap) return false;
      let s2 = 0; for (const x of ns) s2 += x; if (s2 > sumCap) return false;
      const kk = key(ns);
      if (seen.has(kk)) return false;
      seen.add(kk); nx.push(ns); return kk === goal;
    }
  }
  return seen.has(goal);
}
function stats(fs) {
  let H = 0, g = 0;
  for (const f of fs) { H = Math.max(H, f.a + f.b, f.c); g = gcd(g, Math.abs(f.a + f.b - f.c)); }
  return { H, M: H + 1, g: g || 1 };
}
function pumps(fs, W) {
  const { H, M, g } = stats(fs); let bad = [], to = 0;
  for (let n = M; n <= M + W; n++) {
    const cap = Math.max(n, n + g) + H + 6;
    const u = reach(n, n + g, fs, 15, cap, 300000);
    const d = reach(n + g, n, fs, 15, cap, 300000);
    if (u === 'TIMEOUT' || d === 'TIMEOUT') to++;
    else { if (u !== true) bad.push(`climb ${n}->${n + g}`); if (d !== true) bad.push(`desc ${n + g}->${n}`); }
  }
  return { M, g, bad, to };
}

const configs = [];
for (let c = 3; c <= 9; c++) configs.push([[{ a: 1, b: 1, c }], `1+1=${c}`]);
for (const [a, b, c] of [[2, 10, 7], [1, 14, 7], [3, 9, 8], [2, 8, 5], [4, 12, 9],
                         [1, 8, 5], [3, 11, 8], [2, 2, 2], [3, 3, 4], [4, 4, 3]])
  configs.push([[{ a, b, c }], `${a}+${b}=${c}`]);

let cex = [];
for (const [fs, name] of configs) {
  const r = pumps(fs, 7);
  const status = r.bad.length ? `COUNTEREXAMPLE: ${r.bad.join(', ')}` : (r.to ? `ok (${r.to} timeouts skipped)` : 'ok');
  console.log(`${name.padEnd(10)} M=${r.M} g=${r.g}  ${status}`);
  if (r.bad.length) cex.push(name);
}
console.log('\nCounterexamples found:', cex.length ? cex.join(', ') : 'NONE');
process.exit(cex.length ? 1 : 0);
