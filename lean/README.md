# Lean verification

Machine-checked facts about *Ya Stupid* solvability, in **Lean 4 (core only, no
Mathlib)**, checked with **Lean 4.31.0** (pinned in `lean-toolchain`).

## What is proved

`YaStupid.lean` models a board as a `List Nat` and defines, for an arbitrary
finite list of false sums `cfg`, the four legal moves (normal/false split and
normal/false merge, up to reordering via `List.Perm`) and their
reflexive/transitive closure `Reach`.

- **`reach_congr`** — the **necessary condition, for any number of false sums**:
  if a single ball `s` can be turned into a single ball `t`, then `g ∣ (t − s)`
  in ℤ, where `g = gcd_i |(a_i + b_i) − c_i|`. This is the formal backbone of the
  congruence requirement in [`../docs/minimum-value.md`](../docs/minimum-value.md) §2,
  and it holds for an arbitrary `cfg` (the "works for any number of false sums"
  part).
- **`classic_trap`** — the **sharpness witness**: with the single lie
  `9 + 10 = 21`, the pair `21 → 23` is *unsolvable* (`¬ Reach classic [21] [23]`),
  proved via the invariant "positive, and either totalling 19 or being exactly
  `[21]`". This is what makes the guaranteed threshold `M = H + 1 = 22` optimal
  (§5 of the note): both endpoints are `≥ H = 21` and share parity, yet the move
  is impossible.

- **Sufficiency witnesses** (`reach_move`, `reach_trans`, and concrete proofs):
  `classic_19_to_21` and `classic_21_to_19` (both directions in Classic), and
  **`cfg222_5_to_7`** — a checked proof that the lie `2 + 2 = 2` (which makes a
  field of all ones impossible) still solves its in-range puzzle `5 → 7`. Each
  step is a real `Step`; the reorderings are closed by `decide`.
- **`sufficiency_of_pumps`** — the reduction: for *any* configuration, **if** the
  two one-step pumps hold for every `n ≥ M` (climb `[n] → [n+g]` and descend
  `[n+g] → [n]`), **then** every pair `s,t ≥ M` with `g ∣ (t − s)` is solvable.
  Proved via `reach_up_k` / `reach_down_k` (iterate a pump `k` times) and the
  `g ∣ (t−s)` arithmetic.
- **`classic_sufficiency`** — **full sufficiency for Classic mode**, no `sorry`:
  ```
  ∀ s t, 22 ≤ s → 22 ≤ t → (2 : ℤ) ∣ (t − s) → Reach classic [s] [t]
  ```
  Together with `reach_congr` (necessity) and `classic_trap` (sharpness), this
  *completely characterizes* Classic solvability: `[s] → [t]` iff `s,t ≥ 22` and
  `2 ∣ (t−s)`, with `22` sharp. The proof discharges the two Classic pumps via:
  - `reach_frame` / `reach_frame_left` — the frame rule (act on part of the board);
  - `climb_all` / `descD` — a halving recursion (`[n]` for `n ≥ 44` reduces to
    `⌈n/2⌉`, framed and re-merged), bottoming out at the finite base ranges;
  - `baseClimb` (n∈[22,43]) and `baseDesc` (m∈[24,46]) — explicit `Step`-by-`Step`
    witnesses for the finitely many base cases (BFS-found, `decide`-checked perms),
    including the genuinely hard `bc_42 = classic_42_to_44`.

All theorems are checked to depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**, so there are no
gaps. The `#print axioms` lines at the bottom of the file re-confirm this on
every build.

## Toward the symbolic single-sum theorem

For an **arbitrary single false sum** `[⟨a,b,c⟩]` (`a+b ≠ c`):

- **`climb_of_base` / `descend_of_base`** — the halving recursion **generalizes
  symbolically** (frame rule + `reach_move` + `omega` for every div/max bound):
  each one-step pump for `n > 2H` reduces to the base interval.
- **`single_sufficiency_of_base`** — composing with `sufficiency_of_pumps`:
  for any single sum, **if** the climb pump holds on `[M, 2H]` and the descend pump
  on `[M, 2H+g]`, **then** full sufficiency holds (`∀ s,t ≥ M`, `g ∣ (t−s)`).

So symbolic single-sum sufficiency is reduced — `sorry`-free — to a **bounded base
interval**, exactly the shape of the Classic proof (whose base was discharged by
BFS). For any *concrete* single sum the base is finite and dischargeable the same
way, giving a complete proof per instance.

## Full symbolic sufficiency for `a + b < c` with legs `≥ 2` (incl. Classic)

Both base pumps are now discharged symbolically and `sorry`-free, giving
**complete unconditional sufficiency for the whole family `2 ≤ a, b` and
`a + b < c`** — which includes Classic `9+10=21` (`a=9, b=10`):

```
single_sufficiency_dneg : 2 ≤ a → 2 ≤ b → a + b < c →
  ∀ s t, Mval ≤ s → Mval ≤ t → g ∣ (t−s) → Reach [⟨a,b,c⟩] [s] [t]
```

Together with `reach_congr` (necessity) and the sharpness witness, this
**completely characterizes** solvability for every such single sum. In particular
`classic_sufficiency_symbolic` re-derives Classic sufficiency from it with **no BFS
base cases at all**.

### The climb pump (`climb_dneg`)

`climb_of_base` (the halving recursion) fed `baseC_dneg`, which discharges the
entire base interval `[c+1, 2c]` by three explicit symbolic constructions:

- **`climbCleanLow`** (`c+1 ≤ n ≤ 2c−2`) — scatter `[n]` to ones (`getUnits`,
  `scatterClean`, `scatterList`), gather an `a` and a `b` (`gatherPrefix`/`gather`),
  fire `{a,b} → c`, then reel the leftover ones onto the `c` (`mergeUnitsHi`).
- **`climb2cm1`** (`n = 2c−1`) — split to `[c−1, c]`, scatter the `c−1`, build a
  *second* `c`, merge the two `c`s to `2c`, reel the `g−1` carry-ones on.
- **`climb2c`** (`n = 2c`, the stuck value) — `2c` splits only to `{c,c}` (both
  locked), so the trigger cannot be formed at total `2c`. The symbolic analogue of
  Classic's hand-checked `42 → 44`: false-split one `c`, merge its `b` into the
  other `c` to **break the lock without losing `g`**, split that, scatter to ones,
  regather **two** `{a,b}` pairs plus a `g`-one carry, fire both, and merge the two
  fresh `c`s with the carry. Fully general — no `|a−b| ≤ 1` assumption (unlike the
  `19 → {9,10}` shortcut the concrete `42` proof could use).

This single uniform argument **subsumes Classic's 22 BFS-found `baseClimb` lemmas**
(`bc_22 … bc_43`, including the 15-state `classic_42_to_44`).

### The descend pump (`baseD_dneg`)

The key enabler is **`gatherBig`**: when `2 ≤ a, b`, the value `1` is *not* a leg,
so a "+1 accumulator" (`{k,1}` is never `{a,b}`) builds **any** ball from ones with
no cap and no forbidden-pair edge cases. Then **`loseG`** drops a pile of ones by
exactly `g` — build a fresh `c`, false-split it to `{a,b}`, scatter the legs back —
and **`descDrop`** drops a single ball `[m]` to `m−g` ones over the whole base range
`[c+1+g, 2c+2g]`:

- scatterable `m` (`getUnits` for `m ≤ 2c−2`, one split + `getUnits` for
  `m ∈ [2c+2, 2c+2g]` via `scatterHi`) → ones → `loseG`;
- the three `c`-producing values `2c−1, 2c, 2c+1` (`descDrop_2cm1/2c/2cp1`): the
  split exposes a `c` directly, which is false-split and the rest scattered (the
  `2c` case first folds the leftover locked `c` into `a+c`).

`baseD_dneg` then reads `[n+g] → 1^n → [n]` (`descDrop` then `gatherBig`).

## The dual case `a + b > c`: fully closed for the single-cluster family

For `2 ≤ a, b`, `a < c`, `b < c`, `c < a + b`, **and `2(a+b)+2 ≤ 3c`** (e.g.
`3+3=5`, `3+4=6`, `5+5=8`) **both pumps are proved**, so `single_sufficiency_dpos`
gives full sufficiency.  The roles swap: `H = a+b`, `g = a+b−c`, **climb** harvests
a `c` and false-*splits* it (`+g`), **descend** forms `{a,b}` and false-*merges* it
(`−g`).  Legs `< c` give `a+b < 2c`, and `2(a+b)+2 ≤ 3c` keeps `2c` the *only* stuck
value in the base (no `4c, …`), so the scatter-problematic set is again exactly
`{2c−1, 2c, 2c+1}`.

- **Climb** (`climb_dpos` ← `baseC_dpos`): `climbCleanLow_pos` (scatter, build a `c`
  with `gatherBig`, false-split, merge up) + `climb_2cm1_pos/2c/2cp1` for the cluster.
- **Descend** (`baseD_dpos`): the new primitive is **`unlockC`** — a locked `c` plus
  a spare unit becomes `c+1` (normal) and scatters via `getUnits`. With it,
  **`loseGpos`** drops a pile of ones by `g` (fmerge `{a,b}`, then unlock the
  resulting `c`), and **`descToOnes_pos`** drops `[m]` to `m−g` ones — clean values
  scatter then `loseGpos`; the cluster starts false-split *all* their `c`s,
  scatter, and `loseGpos` two/three times.  `solvable_3_3_5` is a concrete corollary.

Reeling ones onto any base uses `mergeUnitsLow` (legs `≥ 2` ⇒ `{v+i,1} ≠ {a,b}`).

## What is *not* (yet) mechanized

1. **The `min(a,b) = 1` sub-case of `a + b < c`.** The `a+b<c` development assumes
   `2 ≤ a, b` (so `gatherBig` is clean). When a leg is `1`, building a `c` from ones
   must route around the one forbidden merge `{1, max(a,b)} = {a,b}` (and `a=b=1` is
   special — the only merge of two ones is the forced `{1,1} → c`). Same shape,
   extra cases.
2. **`a + b > c` outside the single-cluster family** — `2(a+b)+2 > 3c` (so `4c, …`
   also sit in the descend's high start range `[M+g, 2H+2g]`, needing a uniform
   scatter-past-*several*-clusters), a leg `≥ c` (e.g. `2+10=7`), or `c ≤ (a+b)/2`
   (e.g. `2+2=2`).  The `unlockC`/`loseGpos` machinery is the right tool; only the
   multi-cluster bookkeeping remains.

These are intricate but mechanical; they are most comfortable over Mathlib.

Equivalently phrased — the two one-step pumps for an **arbitrary** configuration:

```
climb   : ∀ n, Mval cfg ≤ n → Reach cfg [n] [n + gnat cfg]
descend : ∀ n, Mval cfg ≤ n → Reach cfg [n + gnat cfg] [n]
```

`sufficiency_of_pumps` already reduces *general* sufficiency to these. For Classic
they are discharged above (and now also re-derived symbolically). For a single sum
with `2 ≤ a, b` and `a + b < c` **both pumps are fully proved**; for `a + b > c`
with legs `< c` and `2(a+b)+2 ≤ 3c` **both pumps are fully proved** too.  What
remains is uniform but case-heavy, and wants Mathlib-level `List`/`Multiset`
automation (whose cache is unreachable from the sandbox this was developed in — the
toolchain itself had to be side-loaded from GitHub release assets because the Lean
CDN was blocked).

So the present status: **Classic is completely characterized (necessity +
sufficiency + sharpness, all `sorry`-free) — and now *also* as a corollary of a
fully symbolic theorem. Solvability is completely characterized for every single
sum with `2 ≤ a, b` and either `a + b < c` (`single_sufficiency_dneg`) or
`a + b > c` with legs `< c` and `2(a+b)+2 ≤ 3c` (`single_sufficiency_dpos`,
e.g. `3+3=5`). The remaining gaps are the `min(a,b)=1` edge of `a + b < c` and the
multi-cluster / corner families of `a + b > c`.** Exhaustive search over the
adversarial `{6+7=2, 6+8=3}` (where no `1` ever exists) finds every in-range pump
reachable, so the general pumps are *true* too.

## Check it yourself

With [`elan`](https://github.com/leanprover/elan) installed (it will read
`lean-toolchain` and fetch Lean 4.31.0):

```sh
cd lean
lean YaStupid.lean      # prints the two axiom lines and exits 0 on success
```
