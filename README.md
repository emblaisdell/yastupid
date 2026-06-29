# Ya Stupid

A tiny static physics game built around the *Vine Fallacy*: **9 + 10 = 21**.

You start with one ball and try to reach a single ball of a different number.

- **Tap** a ball to split it. Even → two halves; odd → the two nearest halves.
  A **false‑RHS** value always false‑splits to its ordained pair (`21 → 9, 10`).
- **Drag** from one ball to another to fire a proton beam that draws them
  together; on contact they **merge** into the sum — except the ordained
  **false pair** `{9,10}` which merges to `21`.

Splits and merges conserve the total **except** at the false sum, which is how a
puzzle is solvable at all.

## Modes

- **Classic** — the single lie `9 + 10 = 21`.
- **Advanced** — several "false sums" at once (e.g. `2 + 5 = 3`, `10 + 1 = 2`).

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
