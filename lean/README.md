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
  `g ∣ (t−s)` arithmetic. This is the whole sufficiency argument *except* the two
  pumps themselves.

All theorems are checked to depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**, so there are no
gaps. The `#print axioms` lines at the bottom of the file re-confirm this on
every build.

## What is *not* (yet) mechanized

After `sufficiency_of_pumps`, the **entire** remaining gap is the two one-step
pump lemmas:

```
climb   : ∀ n, Mval cfg ≤ n → Reach cfg [n] [n + gnat cfg]
descend : ∀ n, Mval cfg ≤ n → Reach cfg [n + gnat cfg] [n]
```

Discharging them is exactly trigger formation (§4.1 of the note) and it is
genuinely subtle — *not* a routine carve. The sharpest illustration, in Classic:
the single ball `42` has only the normal split `42 → {21,21}` (both halves are the
locked RHS), so `{9,10}` cannot be assembled at total `42`; reaching `44` must dip
the total through a false move and climb back. A correct, uniform construction of
the pumps for an arbitrary configuration is therefore a real piece of work, most
naturally done over Mathlib (whose prebuilt cache is unreachable from the sandbox
this was developed in — the toolchain itself had to be side-loaded from GitHub
release assets because the Lean CDN was blocked).

So the present status is: **necessity, sharpness, the pump→sufficiency reduction,
and concrete sufficiency witnesses are machine-checked; the two pumps are the lone
remaining lemmas.** An exhaustive search over the adversarial `{6+7=2, 6+8=3}`
configuration (where no `1` ever exists) and over the Classic `42` case finds every
in-range pump reachable, so the pumps are *true* — they are simply not yet
mechanized.

## Check it yourself

With [`elan`](https://github.com/leanprover/elan) installed (it will read
`lean-toolchain` and fetch Lean 4.31.0):

```sh
cd lean
lean YaStupid.lean      # prints the two axiom lines and exits 0 on success
```
