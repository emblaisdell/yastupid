# Lean verification

Machine-checked facts about *Ya Stupid* solvability, in **Lean 4 (core only, no
Mathlib)**, checked with **Lean 4.31.0** (pinned in `lean-toolchain`).

## THE THEOREM

**The characterization is complete.**  For **every** single false sum `a + b = c`
(`a, b, c ≥ 1`) and every pair of single balls `s, t ≥ M = H + 1`
(`H = max(a+b, c)`, `g = |a+b−c|`):

```
single_characterization :  Reach [⟨a,b,c⟩] [s] [t]  ↔  g ∣ (t − s)
```

Sufficiency is **`single_sufficiency_all`**, a case dispatch over every family
closure in this file (see the sections below); necessity is `reach_congr`
(which holds for any number of false sums); sharpness of `M` is witnessed by
`classic_trap`.  Axioms: `[propext, Classical.choice, Quot.sound]` — no `sorry`
anywhere.

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

## `a + b < c` is now complete except `a = b = 1`

The `min(a,b)=1` edge is closed: **`single_sufficiency_dneg_min1`** (`a=1, b≥2`;
by symmetry `b=1, a≥2`, since `{a,b}` is unordered). The climb side needed nothing
new (it only builds legs `≤ max = b` via the capped `gather`). For descend,
**`gatherMin1`** replaces `gatherBig`: it builds any `v ≥ b+2` from ones while
dodging the sole forbidden merge `{1,b}`, by *skipping* `b+1` — build `[b]` and a
spare `[2]`, merge to `b+2`, then reel ones on. Since descend only ever builds the
harvested `c > a+b = b+1` and targets `n ≥ M = c+1` (all `≥ b+2`), `b+1` is never
needed. `solvable_1_2_5` is a concrete corollary.

The only `a+b<c` case left is the doubly-degenerate **`a = b = 1`**, where ones
cannot merge at all (the only merge of two `1`s is the forced `{1,1} → c`).

### All of `a+b>c` with legs `< c`, via the one-pile hub (`single_sufficiency_dpos_full`)

The single-cluster restriction is now **removed**. Instead of per-cluster
constructions, route everything through an all-ones *hub*:

- **`scatterRaw_dpos`** — because both legs are `< c`, splitting strictly reduces
  the max value and the forced `c → {a,b}` lands below `c`, so a strong recursion
  scatters *any* ball to *some* one-pile `1^r` (with `r ≥ v`; the residue
  `g ∣ (r−v)` comes for free from `reach_dvd`).
- **`gainGpos` / `loseGpos`** and the iterators **`onesUpK` / `onesDownK`** walk
  between one-piles in steps of `g`.
- **`gatherBig`** rebuilds the target.

So `[s] → 1^r → 1^t → [t]`, handling **arbitrarily many stuck clusters** uniformly
(`4+4=5`, `5+5=7`, `6+6=7`, …). `solvable_4_4_5` is a genuinely multi-cluster
corollary (`2c=10` and `4c=20` both in range).

### `a = b = 1` closed via 2-seeds (`single_sufficiency_a11`)

The doubly-degenerate edge is now **done too**, so **all of `a + b < c` is fully
mechanized**. The obstruction was that pure ones can only force-merge `{1,1} → c`.
The fix is a **2-seed**: a `2` survives any clean scatter (`keep2`/`keep2hi`), and
`mergeUnitsHi` (base `2 > max(1,1)`) reels ones onto it, so any value is buildable
from `[2] + ones`. Descend reads: get a 2-seed (`reach2seed`), build `[2c]`, split
to `[c,c]`, false-split one `c`, and reel everything onto the other `c` (positioning
via `perm_c_ab`); the cluster starts `2c−1, 2c, 2c+1` harvest the `c` directly.
`solvable_1_1_5` is a concrete corollary.

### `a+b>c` with a leg `≥ c`, isolated to a single hypothesis (`single_sufficiency_legGE`)

The last family is now mechanized **conditionally**, pinning the obstruction to one
crisp spot. When a leg is `≥ c` the all-ones hub breaks at exactly one step —
scattering the legs back after the forced `c → {a,b}` — because `scatterRaw`'s
max-value measure can *rise* there (and for `1+14=7`, `14 = 2c`, greedy scatter
literally loops). Every *other* hub ingredient (`gatherBig`, `gatherPrefix`,
`unlockC`, hence `loseGposGen`) is already leg-`<c`-free. So we package precisely
the broken step as two hypotheses

```
la : Reach [⟨a,b,c⟩] [a] (1^a)      lb : Reach [⟨a,b,c⟩] [b] (1^b)
```

— *"each leg scatters to ones"* — and prove **`single_sufficiency_legGE`**: for
**any** legs (including `≥ c`), `la ∧ lb` gives full sufficiency. The trick is
`scatterRawClean`, a strong recursion that at `v = c` calls `la`/`lb` instead of
recursing into the legs, so it halves on every other value and is well-founded for
*any* `a, b, c`.

This both **generalizes** `single_sufficiency_dpos_full` (when both legs `< c`,
`la`/`lb` are free via `scatterClean`) and **closes concrete leg-`≥ c` instances**:
**`solvable_2_10_7`** fully proves `2 + 10 = 7` (with `b = 10 > c = 7`) `sorry`-free,
discharging `la` directly (`2 < 7`) and `lb` by splitting `10 → [5,5]` first
(`5 < 7`). Both depend only on `[propext, Classical.choice, Quot.sound]`.

### The entire trap diagonal `a = b = c = k`, closed *without* the hub (`single_sufficiency_kkk`)

Bridging is strictly weaker than all-ones reachability. `2+2=2` is the clean
witness: it bridges every `g`-gap above `H+1` (BFS-confirmed) yet **no** single ball
ever reaches a pure-ones pile — `2 = c` is locked (it can only false-split to
`{2,2}`), so a `2` is indestructible and `la`/`lb` are *false*. The same holds for
every `a=b=c=k` (`k ≥ 2`): `k` is indestructible. The hub provably cannot run, so we
use a **different construction** with no ones at all. One recursive helper
**`peelk : [v] → [k, v-k]`** (peel a `k` off any `v ≥ k+1`) drives both pumps
(`H = 2k`, `M = 2k+1`, `g = k`):
- climb `[n] → [n+k]`: peel a `k`, *false-split* it (`k → {k,k}`, `+g`), remerge;
- descend `[n+k] → [n]`: peel two `k`s, *false-merge* them (`{k,k} → k`, `−g`), remerge.

The one twist over `peel2`: for `k ≥ 3` the sub-range `v ∈ [k+1, 2k-2]` cannot expose
a `k` by halving (both halves `< k`), so `peelk_lo` scatters `v` to ones (legal there
— the halving tree stays below `c = k`) and regathers `[k] ++ 1^(v-k)`.

**`single_sufficiency_kkk` closes the whole diagonal `a=b=c=k` for `k ≥ 1`**
(`sorry`-free, standard axioms only), subsuming `single_sufficiency_222`; `k = 1`
(`1+1=1`, degenerate) is handled by the same construction. Concrete corollaries
`solvable_2_2_2`, `solvable_3_3_3`, `solvable_1_1_1`.

### `1+14=7`: the legs *do* scatter — the greedy measure just loops (`escape7_1147`)

`1+14=7` was wrongly lumped with `2+2=2` as a "leg cannot scatter to ones" trap. It
is **not** one. The difference is sharp (both BFS- and Lean-verified):

- in `2+2=2`, `[n]` reaches **no** ones-pile for any count — `2 = c` is genuinely
  indestructible;
- in `1+14=7`, the *greedy* "split the max" measure loops (`14→[7,7]`, `7→{1,14}`, …),
  but the value `7` **escapes**: `fsplit 7→{1,14}` yields a `1`, then `{7,1}→8` is a
  *normal* merge (`≠{1,14}`) and `8→[4,4]` scatters cleanly. So each leg reaches an
  *inflated* ones-pile `1^(b+k·g)` (`g = 8`).

`escape7_1147` (`[7] → 1^15`) and `scatter14_1147` (`[14] → 1^22`) prove the legs
scatter (axioms `[propext, Quot.sound]`). What is *false* is only the exact-count
`[14] → 1^14`: scattering fires `≥ 1` false split, each adding `g`, landing on
`1^(b+k·g)`. So `1+14=7`’s legs satisfy the **inexact** leg-scatter fact, which is
exactly what the hub needs.

**`1+14=7` is now fully closed** (`single_sufficiency_1147`, `solvable_1_14_7`,
`sorry`-free). The inexact-leg hub:
- **`build1147`** builds any `[v]` from ones, dodging the `{1,14}` merge (only `v=15`
  is blocked, built as `[13]+[2]`);
- **`scatter1147`** scatters any `[v]` to some ones-pile (the `7`-escape at `v=7`,
  halving elsewhere);
- **`gainG1147`** gains `2g` (build `7`, `fsplit→{1,14}`, scatter the `14→1^22`),
  **`loseG1147`** loses `g` (gather `14`, `fmerge{1,14}→7`, unlock via `unlock7`),
  and **`gainOneG1147`** nets `+g` by gaining `2g` then shedding `g`;
- then scatter `[s]→1^r`, walk by `g`, rebuild `[t]`.

### The abstract hub — four primitives ⇒ sufficiency (`sufficiency_from_hub`)

`dpos_full`, `legGE`, and `1147` are the same hub argument over different leg
constructions. **`sufficiency_from_hub`** states it once: for any `a+b>c`, the four
primitives `bld` (build `[v]` from ones), `losG` (drop `g`), `ganG` (gain *some*
`j·g`, `j ≥ 1`), `scat` (scatter `[v]` to some ones-pile) give full sufficiency. The
crux `hub_gainOne` turns one `ganG` (`+j·g`) plus `j−1` leg-free `losG`s into a net
`+g`, so inexactly-scattering legs are fine. `single_sufficiency_1147_via_hub`
re-derives `1+14=7` through it (with `j=2`), confirming the abstraction is faithful.
Every remaining `a+b>c`, leg-`≥ c` config now reduces to discharging these four — and
`scat` is the only genuinely config-specific one.

### The `scatBig` reservoir trick and the families it closes

The hub primitives are now discharged for **broad infinite families** by one device,
`scatBig`: with a single spare unit, *any* `[v]` scatters to ones using only **normal**
moves — a locked `c` is bumped `{c,1}→c+1` (normal, since `1 ∉ {a,b}`) and `c+1 ≤ 2c-2`
scatters (needs `c ≥ 3`). Being total-preserving, it makes the **gain pump exact and
unconditional** (`ganG_uncond`: build `c` at the reservoir's end, `scatBig` both legs
left-to-right). So for `2 ≤ a, b`, `c ≥ 3`, `c < a+b`, three of the four primitives are
free, and **`single_sufficiency_legGE_inexact`** reduces sufficiency to just *"do the
legs scatter (to some `1^(b+kg)`)?"*. Discharging that bootstrap (the small leg seeds
the first unit) closes:

- **`⟨1,b,c⟩`, `3 ≤ c < b`** (all `b`, inexact included) — `single_sufficiency_a1`
  (e.g. `1+10=5`, `1+12=7`); the `a=1` builder dodges `{1,b}`.
- **`⟨a,b,c⟩`, `2 ≤ a < 2c`, `a ≠ c`, `c ≤ b`** — `single_sufficiency_g` (e.g. `5+5=3`,
  `2+14=7`), the small leg `< 2c` bootstrapping; the big leg is any size.

### All bands at once via `Scat`, and one `Scat` leg suffices

The band-by-band recursion is captured once by the inductive **`Scat c v`** ("`v`
halves — floor or ceil — into the window `(c,2c)`"), which holds for **every `v`
except the fixed points `c·2^k`**.  `scatStandaloneScat` scatters any `Scat` value to
`1^v` by induction.  Better, **`scatAll`** shows that once `c` itself scatters, *every*
`[v]` does — and `c` scatters as soon as **one** leg is `Scat`.  So
**`single_sufficiency_oneScat`** closes every `2 ≤ a,b`, `c ≥ 3`, `c < a+b` config with
**at least one leg not of the form `c·2^k`** — the other leg may be anything, even
`c·2^k` (e.g. `8+9=4`, where `8 = 2c`).  This subsumes all the families above.

### The `a=b` traps, closed without ones (`single_sufficiency_aac`)

The genuine traps — where `[M]` reaches *no* ones-pile — are closed for the `a=b`
case by a construction that **never scatters to ones**.  `peelc` peels copies of the
locked `c` (only ever scattering values `< c`); **`gatherCval`** then builds `[a]` by
*merging copies of `c`* (`{c, jc} → (j+1)c`, all normal since `c ≠ a`).  Climb peels
one `c`, false-splits `c→{a,a}`, remerges; descend peels `2(a/c)` copies of `c`,
gathers two `[a]`s, false-merges `{a,a}→c`.  **`single_sufficiency_aac`** closes every
`⟨a,a,c⟩` with `c ∣ a`, `c < a`, `3 ≤ c` — including all `a=b` `c·2^k` traps (`6+6=3`,
`10+10=5`, `12+12=3`, …).  `solvable_6_6_3` is a concrete corollary.

### The `a ≠ b` `c·2^k` traps, closed (`single_sufficiency_trap`)

The genuine `a ≠ b` traps `⟨c·2^i, c·2^j, c⟩` (`i ≠ j`, `c ≥ 3` — `3+6=3`, `6+12=3`,
`3+12=3`, …) are closed by generalizing the `a=b` escape to `⟨a,b,c⟩`.  A **parameterized
peeler** `hpeel : ∀ v ≥ c+1, [v] → [c, v−c]` drives the climb (peel `c`, false-split,
merge) and descend (peel `2^i+2^j` copies of `c`, rebuild `[a]`,`[b]`, false-merge);
the rebuild uses **`powMerge`** (binary doubling `{x,x}→2x`, always legal since `a ≠ b`).
The peeler is `peelcG` (generic, recursion coincidence-free when `|a−b| ∉ {c,c+1}`); the
lone pathological shape `⟨c,2c,c⟩` (`b = a+c`) — where the recursion *does* hit `{c,2c}`
at `v = 4c` — is handled by `peelc_c2c`, which routes that single value through the
bespoke 11-move **`peel4c`** (`[4c] → [c,3c]`, dipping to total `8c`).  `reach_swap`
makes the closure order-independent.  Worked: `solvable_3_6_3`, `solvable_6_12_3`.

### `c = 2` both-even traps, closed (`single_sufficiency_c2_both_even`)

For `c = 2` the all-ones field is generally unreachable.  When **both legs are even**
(`a = 2·ma`, `b = 2·mb`, legs `≥ 3`) the *copies-of-`2`* hub closes the config: the
uniform peeler **`peelc2`** peels a `2` off any `v ≥ 3` (when its recursion would hit
`{a,b}`, forcing `|a−b| ∈ {2,3}`, it peels a `2` off *both* halves and merges the two
near-equal residues, which differ by `≤ 1` and so are never `{a,b}`), and the
**`descendSeq`** sequential gather (`gatherCvalG`, `{c,kc}→(k+1)c`, always safe since
each intermediate `kc` is below the leg) rebuilds the legs.  Closes every both-even
`c=2` trap including the adjacent `b=a+2` case (`4+4=2`, `4+6=2`, `4+8=2`, `6+6=2`, …).
`single_sufficiency_div` is the general divisible-leg form (`c ∣ a`, `c ∣ b`, `c ≥ 2`).

### `c = 2`, every leg parity (legs `≥ 3`) — **completely closed**

All four parity classes of `⟨a,b,2⟩` with both legs `≥ 3` are now closed:
- `single_sufficiency_c2_aa` — `a = b` (any parity; `3+3=2`, `5+5=2`): build `[2a]` from
  `a` copies of `2`, **split** `[2a] → [a,a]`, false-merge `{a,a} → 2`.  Works for odd
  `a`, where `descendSeq` (needs `2 ∣ a`) does not.
- `single_sufficiency_c2_both_odd` — both odd, `a ≠ b` (`3+5=2`, `5+7=2`): build
  `[2a] → [a,a]`, bridge one `[a]` to `[b]` with `d = (b−a)/2` more `2`s (`mergeTwos`).
- `single_sufficiency_c2_odd_even` — one odd, one even (`4+5=2`, `3+4=2` via `reach_swap`):
  even leg from `2`s, odd leg `b = 3+2f` from a `[3]` seed produced by the gadget
  `[2,2,2] → [6] → [3,3] → [1,2,3]`; the spare `1` and `2` merge harmlessly into the
  leftover (`1, 2 ∉ {a,b}`).

Crucially none of these needs a `1`-source from `[n+g]`: odd legs are reached by
**splitting an even ball** (`6 → {3,3}`), and a targeted bidirectional BFS confirms even a
power-of-`2` source descends with **no false split**.

### `c = 2` with a leg `= c` (`⟨2,b,2⟩`) — closed

`single_sufficiency_2b2` closes **every** `⟨2,b,2⟩` (`b ≥ 3`), and `⟨a,2,2⟩` follows by
`reach_swap` (`⟨2,2,2⟩` is `single_sufficiency_222`).  Here `a = c = 2`, so *every*
`{x,2}` merge is the forbidden pair when `x = b`.  `peel2G` peels a `2` via a two-route
recursion; `descend2_odd` builds the odd leg from a `[3]` seed and uses the gadget's
spare `2` as the false-merge partner and its spare `1` (safe: `1 ∉ {2,b}`) to repair the
leftover.  Even `b` reuses `single_sufficiency_div`; `b = 4` is `⟨c,2c,c⟩` at `c = 2`
(via the `c ≥ 2`-relaxed `single_sufficiency_c2c`).

### Unit-leg `⟨1,b,2⟩` (`c = 2`) — closed

`single_sufficiency_1b2` closes every `⟨1,b,2⟩` (`b ≥ 3`), and `⟨b,1,2⟩` by `reach_swap`.
Ones are reachable here (`2 → {1,b}`), so `climb_a1_b2` peels a `2` (`peel2_a1`, two-route;
the lone both-bad value `⟨1,3,2⟩` at `v = 6` uses `special6_132`) and false-splits it,
while `descend_a1_b2_{odd,even}` build `[b]` from `2`s and take the gadget's spare `1` as
the false-merge partner `{1,b}→2`.

### The doubly-degenerate trap `⟨1,c,c⟩` — closed

`single_sufficiency_1cc_all` closes `⟨1,c,c⟩` for **every** `c ≥ 2` (`⟨c,1,c⟩` by swap).
This is a genuine trap — `[c]` only false-splits to `{1,c}`, regenerating the `c`, so
pure ones are unreachable, and naive peeling is *provably* impossible (`[c] → [1,c−1]`
and even `[5] → [1,4]` in `⟨1,3,3⟩` are unreachable).  The escape (`g = 1`):
**`loseOne`** recursively peels `c`s off the remainder and, at the sub-`c` base,
scatters to ones and rides ONE false-merge `{1,c}→c` (losing exactly `1`); when
`c ∣ n+1` (the pile would peel to all `c`s), `descend_1cc_dvd` first climbs `+1`, peels
to `c^(K−1) ++ [c+1]`, scatters the `c+1`, and rides TWO false-merges.  For `c = 2`
(`⟨1,2,2⟩`) the divisible case instead runs the odd-ball core
`{2,2}→4, {4,2}→6, 6→{3,3}, 3→{1,2}` (`rA_122`), sourcing two `1`s by *splitting*
rather than false-splitting, and rides one false-merge.

### The `c = 1` family `⟨a,b,1⟩` — closed

`single_sufficiency_c1` closes every `⟨a,b,1⟩` (`b ≥ 2`; `⟨1,1,1⟩` is `kkk 1`,
`⟨a,1,1⟩` by swap).  With `c = 1` nothing is blocked from normal splitting
(`scatAll1`), so a ones-hub runs; the only care is dodging the `{a,b}` merge and — for
`a = 1` — the poisoned `{1,b}` pair (skipped via a `[b−1]+[2]` or `[2]+[2]` rebuild).

## Everything is closed

**There is no open case.**  `single_sufficiency_all` assembles all of the above into
the complete dispatch — for every `a, b, c ≥ 1` (including `a+b = c`, where `g = 0`
and the statement is trivial), every `s,t ≥ M` with `g ∣ (t−s)` are interreachable —
and `single_characterization` states the two-directional iff.  The assembly rests on
three glue lemmas: **`suff_swap`** (sufficiency transfers across `⟨a,b,c⟩ ↦ ⟨b,a,c⟩`,
via `reach_swap` + `Mval`/`gz` swap-invariance), **`pow_or_scat`** (every `v ≥ c` is
`2^k·c` or `Scat c v` — so a non-Scat leg *is* a trap leg), and **`pow2_eq_succ`**
(`2^q = 2^p + 1` forces `p=0, q=1`, isolating the pathological `⟨c,2c,c⟩` shape).

The two one-step pumps

```
climb   : ∀ n, Mval cfg ≤ n → Reach cfg [n] [n + gnat cfg]
descend : ∀ n, Mval cfg ≤ n → Reach cfg [n + gnat cfg] [n]
```

are therefore discharged for **every single false sum**; `sufficiency_of_pumps` turns
them into full sufficiency, `reach_congr` gives necessity (for any number of false
sums), and `classic_trap` gives sharpness of `M = H+1`.  Independent BFS
(`test/counterexample-search.js` plus targeted bidirectional sweeps over the traps,
the whole `c=2` family, and the `a=1` families) corroborates: no counterexample
anywhere.

## Check it yourself

With [`elan`](https://github.com/leanprover/elan) installed (it will read
`lean-toolchain` and fetch Lean 4.31.0):

```sh
cd lean
lean YaStupid.lean      # prints the two axiom lines and exits 0 on success
```
