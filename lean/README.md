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

## What is *not* (yet) mechanized

**Classic mode is fully done.** What remains open is the two one-step pumps for an
**arbitrary** configuration:

```
climb   : ∀ n, Mval cfg ≤ n → Reach cfg [n] [n + gnat cfg]
descend : ∀ n, Mval cfg ≤ n → Reach cfg [n + gnat cfg] [n]
```

`sufficiency_of_pumps` already reduces *general* sufficiency to these. For Classic
they are discharged above (halving recursion + finite base cases). For a general
config the same recursion idea should work, but the base set is no longer a fixed
small interval and the carving interacts with arbitrarily many locked values and
forbidden pairs — so it wants Mathlib-level `List`/`Multiset` automation (whose
cache is unreachable from the sandbox this was developed in; the toolchain itself
had to be side-loaded from GitHub release assets because the Lean CDN was blocked).

So the present status: **Classic is completely characterized (necessity +
sufficiency + sharpness, all `sorry`-free); for arbitrary configurations,
necessity and the pump→sufficiency reduction are done, and the two general pumps
are the remaining piece.** Exhaustive search over the adversarial `{6+7=2, 6+8=3}`
(where no `1` ever exists) finds every in-range pump reachable, so they are *true*.

## Check it yourself

With [`elan`](https://github.com/leanprover/elan) installed (it will read
`lean-toolchain` and fetch Lean 4.31.0):

```sh
cd lean
lean YaStupid.lean      # prints the two axiom lines and exits 0 on success
```
