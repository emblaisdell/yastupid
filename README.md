# Ya Stupid

A tiny static physics game built around the *Vine Fallacy*: **9 + 10 = 21**.

You drop straight into a random, always‑solvable puzzle (no menus): start with one
ball, end with a single ball showing the target.

- **Tap** a ball to split it. Even → two halves; odd → the two nearest halves.
  A **magic** value always false‑splits to its ordained pair (`21 → 9, 10`) —
  these wear a dashed ring.
- **Drag** from one ball to another to fire a proton beam that draws them
  together; on contact they **merge** into the sum — except the ordained
  **false pair** `{9,10}` which merges to `21`.

Splits and merges conserve the total **except** at the false sum, which is how a
puzzle is solvable at all. Every generated puzzle has both endpoints in
`[M, 99]` and `t ≡ s (mod g)`, so it is provably solvable.

## Modes

- **Classic** — the single lie `9 + 10 = 21`  (`g=2`, `M=22`).
- **Advanced** — three lies at once: `9 + 10 = 21`, `2 + 5 = 3`, `10 + 1 = 2`
  (`g=1`, `M=22` — so any target works, not just same‑parity).

## The math

A puzzle `s → t` is solvable when `t ≡ s (mod g)` and both are at least `M`,
where for false sums `(a_i, b_i, c_i)` with inaccuracy `d_i = (a_i+b_i) − c_i`:

```
g = gcd_i |d_i|
H = max_i max(a_i + b_i, c_i)
M = H + 1            (the sharp guaranteed threshold)
```

Classic: `g = 2`, `H = 21`, `M = 22`. The bound is sharp because of the **21
trap** (`21 ↛ 23`). Full statement, proof, and sharpness are in
[`docs/minimum-value.md`](docs/minimum-value.md).

## Run locally

It's a static site — just serve the folder:

```
python3 -m http.server 8080      # then open http://localhost:8080
```

## Verify the math / levels

```
node test/verify.js              # BFS reachability checks + sharpness spot-checks
```

## Files

```
index.html             markup + HUD
css/style.css          styling (mobile-first, responsive)
js/game.js             engine: physics, gestures, rules, levels
docs/minimum-value.md  the minimum-value theorem and proof
test/verify.js         brute-force reachability verifier
```
