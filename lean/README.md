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

All theorems are checked to depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**, so there are no
gaps. The `#print axioms` lines at the bottom of the file re-confirm this on
every build.

## What is *not* (yet) mechanized

The **universal sufficiency** statement (`∀ s,t ≥ M` with `g ∣ (t − s)`, solvable)
is proved on paper in the note (§4: Bézout pumps that stay above `H`, plus
**Lemma 1, trigger formation**). It is **not** formalized here. An earlier draft
proved carving via an "all-ones" field, which is *false* in general
(`2 + 2 = 2` never reduces to ones) — so the corrected proof builds triggers by
recombination, and mechanizing that for an arbitrary configuration is a
substantial undertaking, most naturally over Mathlib (whose prebuilt cache is
unreachable from the sandbox this was developed in — the toolchain itself had to
be side-loaded from GitHub release assets because the Lean CDN was blocked). What
*is* machine-checked are the two ends that pin the threshold (necessity and the
sharpness trap) plus the worked sufficiency witnesses above; the universal middle
is the open piece.

## Check it yourself

With [`elan`](https://github.com/leanprover/elan) installed (it will read
`lean-toolchain` and fetch Lean 4.31.0):

```sh
cd lean
lean YaStupid.lean      # prints the two axiom lines and exits 0 on success
```
