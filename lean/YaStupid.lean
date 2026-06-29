/-
  Ya Stupid — machine-checked facts about solvability.
  Lean 4 (core only, no Mathlib).  Checked with Lean 4.31.0.

  A board is a `List Nat` of ball values.  For an arbitrary finite list of false
  sums `cfg`, one legal move (`Step`) either

    * normal-splits a value `n ≥ 2` that is not a false RHS into ⌊n/2⌋, ⌈n/2⌉,
    * false-splits a false RHS `c` into its ordained pair `a, b`,
    * normal-merges two values that are not an ordained pair into their sum,
    * false-merges an ordained pair `a, b` into `c`,

  all up to reordering (`List.Perm`).  `Reach` is its reflexive/transitive closure.

  MAIN RESULTS
  ------------
  * `reach_congr`  — NECESSARY CONDITION, for ANY number of false sums:
        if `[s] → [t]` is reachable then `g ∣ (t − s)` in ℤ, where
        `g = gcd_i |(a_i + b_i) − c_i|`.
  * `classic_trap` — SHARPNESS witness: with the single lie `9 + 10 = 21`,
        `21 → 23` is UNSOLVABLE, so the guaranteed threshold `M = H + 1 = 22`
        cannot be lowered (both 21 and 23 are ≥ H = 21 and share parity).
-/

namespace YaStupid

/-- A false sum: the pair `{a,b}` merges to `c`, and `c` splits to `{a,b}`. -/
structure FalseSum where
  a : Nat
  b : Nat
  c : Nat
deriving DecidableEq, Repr

abbrev Config := List FalseSum

/-- Total value on the board. -/
def total (l : List Nat) : Nat := l.foldr (· + ·) 0

@[simp] theorem total_nil  : total [] = 0 := rfl
@[simp] theorem total_cons (x : Nat) (l) : total (x :: l) = x + total l := rfl

theorem total_append (l m : List Nat) : total (l ++ m) = total l + total m := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem total_perm {l m : List Nat} (h : l.Perm m) : total l = total m := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp only [total_cons]; omega
  | trans _ _ ih₁ ih₂ => omega

/-- Inaccuracy of a false sum, as an integer: `(a + b) − c`. -/
def FalseSum.delta (f : FalseSum) : Int := (f.a : Int) + f.b - f.c

/-- `g` = gcd of the absolute inaccuracies (`0` if there are no false sums). -/
def gnat (cfg : Config) : Nat := cfg.foldr (fun f acc => Nat.gcd f.delta.natAbs acc) 0

/-- `g`, as an integer. -/
def gz (cfg : Config) : Int := (gnat cfg : Int)

theorem gnat_dvd_natAbs {cfg : Config} {f : FalseSum} (hf : f ∈ cfg) :
    gnat cfg ∣ f.delta.natAbs := by
  induction cfg with
  | nil => cases hf
  | cons hd tl ih =>
    have hstep : gnat (hd :: tl) = Nat.gcd hd.delta.natAbs (gnat tl) := rfl
    rw [hstep]
    rcases List.mem_cons.1 hf with h | h
    · subst h; exact Nat.gcd_dvd_left _ _
    · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (ih h)

theorem gz_dvd_delta {cfg : Config} {f : FalseSum} (hf : f ∈ cfg) : gz cfg ∣ f.delta := by
  have h : (gnat cfg : Int) ∣ (f.delta.natAbs : Int) :=
    Int.natCast_dvd_natCast.2 (gnat_dvd_natAbs hf)
  exact Int.dvd_natAbs.1 h

/-- The four local rewrites, parameterised by the config. -/
inductive Local (cfg : Config) : List Nat → List Nat → Prop
  | nsplit (n : Nat) : 2 ≤ n → (∀ f ∈ cfg, f.c ≠ n) →
      Local cfg [n] [n / 2, (n + 1) / 2]
  | fsplit (f : FalseSum) : f ∈ cfg → Local cfg [f.c] [f.a, f.b]
  | nmerge (x y : Nat) : (∀ f ∈ cfg, ¬ ((f.a = x ∧ f.b = y) ∨ (f.a = y ∧ f.b = x))) →
      Local cfg [x, y] [x + y]
  | fmerge (f : FalseSum) : f ∈ cfg → Local cfg [f.a, f.b] [f.c]

/-- One legal move, applied to part of the board, closed under reordering. -/
def Step (cfg : Config) (s t : List Nat) : Prop :=
  ∃ ain aout rest, Local cfg ain aout ∧ s.Perm (ain ++ rest) ∧ t.Perm (aout ++ rest)

/-- Reachability: reflexive/transitive closure of `Step`. -/
inductive Reach (cfg : Config) : List Nat → List Nat → Prop
  | refl (s) : Reach cfg s s
  | step {s t u} : Step cfg s t → Reach cfg t u → Reach cfg s u

theorem dvd_neg' {a b : Int} (h : a ∣ b) : a ∣ -b := by
  obtain ⟨k, hk⟩ := h; exact ⟨-k, by rw [hk, Int.mul_neg]⟩

/-! ### The necessary condition (any number of false sums) -/

/-- Every local rewrite changes the total by a multiple of `g`. -/
theorem local_dvd (cfg : Config) {ain aout : List Nat} (h : Local cfg ain aout) :
    gz cfg ∣ ((total aout : Int) - total ain) := by
  cases h with
  | nsplit n hn hc =>
    have hk : total [n / 2, (n + 1) / 2] = n := by simp only [total_cons, total_nil]; omega
    have h1 : total [n] = n := by simp
    rw [hk, h1]; simp
  | fsplit f hf =>
    have hd : (total [f.a, f.b] : Int) - total [f.c] = f.delta := by
      simp only [total_cons, total_nil, FalseSum.delta]; omega
    rw [hd]; exact gz_dvd_delta hf
  | nmerge x y _ =>
    have hd : (total [x + y] : Int) - total [x, y] = 0 := by
      simp only [total_cons, total_nil]; omega
    rw [hd]; simp
  | fmerge f hf =>
    have hd : (total [f.c] : Int) - total [f.a, f.b] = - f.delta := by
      simp only [total_cons, total_nil, FalseSum.delta]; omega
    rw [hd]; exact dvd_neg' (gz_dvd_delta hf)

/-- One step changes the total by a multiple of `g`. -/
theorem step_dvd {cfg : Config} {s t : List Nat} (h : Step cfg s t) :
    gz cfg ∣ ((total t : Int) - total s) := by
  obtain ⟨ain, aout, rest, hl, hps, hpt⟩ := h
  have hs : total s = total ain + total rest := by rw [total_perm hps, total_append]
  have ht : total t = total aout + total rest := by rw [total_perm hpt, total_append]
  have key : (total t : Int) - total s = (total aout : Int) - total ain := by omega
  rw [key]; exact local_dvd cfg hl

/-- Reaching `t` from `s` changes the total by a multiple of `g`. -/
theorem reach_dvd {cfg : Config} {s t : List Nat} (h : Reach cfg s t) :
    gz cfg ∣ ((total t : Int) - total s) := by
  induction h with
  | refl s => simp
  | @step s t u hst _ ih =>
    have h1 := step_dvd hst
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := h1
    exact ⟨p + q, by rw [Int.mul_add, ← hp, ← hq]; omega⟩

/-- **Necessary condition (any number of false sums).**  If a single ball `s`
    can be turned into a single ball `t`, then `g ∣ (t − s)`. -/
theorem reach_congr {cfg : Config} {s t : Nat} (h : Reach cfg [s] [t]) :
    gz cfg ∣ ((t : Int) - s) := by
  have := reach_dvd h; simpa using this

/-! ### Sharpness: the Classic "21 trap" -/

/-- Classic mode: the single lie `9 + 10 = 21`. -/
def classic : Config := [⟨9, 10, 21⟩]

/-- For the record: `g = 2` in Classic mode. -/
theorem gnat_classic : gnat classic = 2 := by decide

/-- All balls carry a positive value. -/
def Pos (l : List Nat) : Prop := ∀ x ∈ l, 1 ≤ x

/-- Invariant maintained from a lone `21`: positive, and either totalling `19`
    or being exactly the single ball `21`. -/
def Inv (s : List Nat) : Prop := Pos s ∧ (total s = 19 ∨ s.Perm [21])

theorem pos_total_zero {l : List Nat} (hp : Pos l) (h : total l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs => have hx := hp x (by simp); simp only [total_cons] at h; omega

theorem pos_append {l m : List Nat} (hl : Pos l) (hm : Pos m) : Pos (l ++ m) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact hl x h
  · exact hm x h

theorem pos_perm {l m : List Nat} (hp : l.Perm m) (h : Pos l) : Pos m :=
  fun x hx => h x (hp.mem_iff.2 hx)

theorem inv_step {s t : List Nat} (h : Step classic s t) (hs : Inv s) : Inv t := by
  obtain ⟨ain, aout, rest, hl, hps, hpt⟩ := h
  obtain ⟨hpos, hval⟩ := hs
  have hposrest : Pos rest :=
    fun x hx => hpos x (hps.mem_iff.2 (List.mem_append.2 (Or.inr hx)))
  have hposain : Pos ain :=
    fun x hx => hpos x (hps.mem_iff.2 (List.mem_append.2 (Or.inl hx)))
  cases hl with
  | nsplit n hn hc =>
    have hts : total s = n + total rest := by
      rw [total_perm hps, total_append]; simp only [total_cons, total_nil]; omega
    have htt : total t = n + total rest := by
      rw [total_perm hpt, total_append]; simp only [total_cons, total_nil]; omega
    have haout : Pos [n / 2, (n + 1) / 2] := by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h <;> omega
    refine ⟨pos_perm hpt.symm (pos_append haout hposrest), ?_⟩
    rcases hval with hv | hv
    · left; omega
    · exfalso
      have heq : n :: rest = [21] := by simpa using List.perm_singleton.1 (hps.symm.trans hv)
      injection heq with hn21 hrest
      exact (hc ⟨9, 10, 21⟩ (by simp [classic])) hn21.symm
  | fsplit f hf =>
    have hfe : f = ⟨9, 10, 21⟩ := by simpa [classic] using hf
    subst hfe
    have hts : total s = 21 + total rest := by
      rw [total_perm hps, total_append]; simp only [total_cons, total_nil]
    have htt : total t = 19 + total rest := by
      rw [total_perm hpt, total_append]; simp only [total_cons, total_nil]
    have haout : Pos [9, 10] := by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h <;> omega
    refine ⟨pos_perm hpt.symm (pos_append haout hposrest), ?_⟩
    rcases hval with hv | hv
    · exfalso; omega
    · have hlen := (hps.symm.trans hv).length_eq
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      have hr : rest = [] := List.length_eq_zero_iff.1 (by omega)
      subst hr; left; simpa using htt
  | nmerge x y _ =>
    have hts : total s = (x + y) + total rest := by
      rw [total_perm hps, total_append]; simp only [total_cons, total_nil]; omega
    have htt : total t = (x + y) + total rest := by
      rw [total_perm hpt, total_append]; simp only [total_cons, total_nil]; omega
    have haout : Pos [x + y] := by
      intro z hz; have hx := hposain x (by simp); simp only [List.mem_singleton] at hz; omega
    refine ⟨pos_perm hpt.symm (pos_append haout hposrest), ?_⟩
    rcases hval with hv | hv
    · left; omega
    · exfalso
      have hlen := (hps.symm.trans hv).length_eq
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | fmerge f hf =>
    have hfe : f = ⟨9, 10, 21⟩ := by simpa [classic] using hf
    subst hfe
    have hts : total s = 19 + total rest := by
      rw [total_perm hps, total_append]; simp only [total_cons, total_nil]
    have haout : Pos [21] := by intro z hz; simp only [List.mem_singleton] at hz; omega
    refine ⟨pos_perm hpt.symm (pos_append haout hposrest), ?_⟩
    rcases hval with hv | hv
    · have hr : rest = [] := pos_total_zero hposrest (by omega)
      subst hr; right; simpa using hpt
    · exfalso
      have hlen := (hps.symm.trans hv).length_eq
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega

theorem inv_reach {s t : List Nat} (h : Reach classic s t) : Inv s → Inv t := by
  induction h with
  | refl s => exact id
  | step hst _ ih => exact fun hs => ih (inv_step hst hs)

/-- **Sharpness.**  In Classic mode, `21 → 23` is impossible. -/
theorem classic_trap : ¬ Reach classic [21] [23] := by
  intro h
  have hi : Inv [21] :=
    ⟨fun x hx => by have : x = 21 := List.mem_singleton.1 hx; omega, Or.inr (List.Perm.refl _)⟩
  obtain ⟨_, hv⟩ := inv_reach h hi
  rcases hv with h19 | hp
  · simp only [total_cons, total_nil] at h19; omega
  · have h2321 : (23 : Nat) = 21 := by simpa using List.perm_singleton.1 hp
    omega

/-! ### Sufficiency — building blocks and worked witnesses

The §4 "field of all ones" lemma is *false* in general: with `2 + 2 = 2`, tapping
a `2` yields `{2,2}` (it never reduces to `1`s). So sufficiency cannot route
through all-ones. The witnesses below are constructed directly and show the pump
mechanism still works — in particular that `2 + 2 = 2` does **not** trap an
in-range puzzle. Each step is an honest `Step`; the permutations are closed by
`decide`. -/

/-- Compose reachability. -/
theorem reach_trans {cfg : Config} {a b c : List Nat}
    (h1 : Reach cfg a b) (h2 : Reach cfg b c) : Reach cfg a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact Reach.step s (ih h2)

/-- Take one local move on the `ain` part of `a` (the rest is carried along),
    then continue.  `ain`/`aout` are pinned by `hl`; `rest` is explicit. -/
theorem reach_move {cfg : Config} {a ain aout : List Nat} (rest : List Nat)
    (hl : Local cfg ain aout) (hp : a.Perm (ain ++ rest))
    {b : List Nat} (hr : Reach cfg (aout ++ rest) b) : Reach cfg a b :=
  Reach.step ⟨ain, aout, rest, hl, hp, List.Perm.refl _⟩ hr

/-- Classic, climbing: `19 → 21` (normal-split 19 to {9,10}, then false-merge). -/
theorem classic_19_to_21 : Reach classic [19] [21] :=
  reach_move [] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  Reach.refl _

/-- Classic, descending: `21 → 19` (false-split 21, then re-merge around the
    forbidden {9,10} pair).  Shows the move set reaches both directions. -/
theorem classic_21_to_19 : Reach classic [21] [19] :=
  reach_move [] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [5] (Local.nmerge 4 10 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 14 5 (by decide)) (by decide) <|
  Reach.refl _

/-- The pathological config `2 + 2 = 2`. -/
def cfg222 : Config := [⟨2, 2, 2⟩]

/-- **`2 + 2 = 2` does not trap solvability.**  `M = H + 1 = 5` here, and the
    in-range puzzle `5 → 7` is solved — even though a field of all ones is
    unreachable.  The route gets a `1` from the odd `3` (which splits normally),
    false-splits a `2` for the `+2`, then merges back avoiding the `{2,2}` pair. -/
theorem cfg222_5_to_7 : Reach cfg222 [5] [7] :=
  reach_move []      (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [2]     (Local.nsplit 3 (by decide) (by decide)) (by decide) <|
  reach_move [1, 2]  (Local.fsplit ⟨2, 2, 2⟩ (by decide))     (by decide) <|
  reach_move [2, 2]  (Local.nmerge 1 2 (by decide))           (by decide) <|
  reach_move [2]     (Local.nmerge 3 2 (by decide))           (by decide) <|
  reach_move []      (Local.nmerge 5 2 (by decide))           (by decide) <|
  Reach.refl _

/-- The hardest Classic climb, machine-checked.  `[42]` splits only to `{21,21}`
    (both locked), so `{9,10}` cannot be formed at total 42; reaching `44` must dip
    the total to 40, escape the lock, **re-create a fresh `{9,10}` by normal-splitting
    a `19`** (`19 → 9,10`), and ride two false-merges back up.  15 states. -/
theorem classic_42_to_44 : Reach classic [42] [44] :=
  reach_move []          (Local.nsplit 42 (by decide) (by decide)) (by decide) <|
  reach_move [21]        (Local.fsplit ⟨9, 10, 21⟩ (by decide))    (by decide) <|
  reach_move [10, 21]    (Local.nsplit 9 (by decide) (by decide))  (by decide) <|
  reach_move [5, 10, 21] (Local.nsplit 4 (by decide) (by decide))  (by decide) <|
  reach_move [2, 10, 21] (Local.nmerge 2 5 (by decide))            (by decide) <|
  reach_move [2, 7]      (Local.nmerge 10 21 (by decide))          (by decide) <|
  reach_move [2]         (Local.nmerge 7 31 (by decide))           (by decide) <|
  reach_move [2]         (Local.nsplit 38 (by decide) (by decide)) (by decide) <|
  reach_move [2, 19]     (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 10]  (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 10]  (Local.fmerge ⟨9, 10, 21⟩ (by decide))    (by decide) <|
  reach_move [9, 10]     (Local.nmerge 2 21 (by decide))           (by decide) <|
  reach_move [23]        (Local.fmerge ⟨9, 10, 21⟩ (by decide))    (by decide) <|
  reach_move []          (Local.nmerge 21 23 (by decide))          (by decide) <|
  Reach.refl _

/-! ### Full sufficiency, reduced to the two one-step pumps

The clean "carve a trigger at fixed total, fire once" picture is *not* enough on
its own — e.g. in Classic the single ball `42` has only the normal split
`42 → {21,21}` (both halves locked), so `{9,10}` cannot be formed at total `42`;
reaching `44` must dip the total via a false move and climb back. A correct, fully
general construction of the one-step pumps is therefore subtle (it is the open
piece; see the note). What we *do* mechanize here, with no `sorry`, is the
reduction: **once the two pumps hold for a configuration, every congruent pair
above `M` is solvable.** -/

/-- `H = max_i max(a_i+b_i, c_i)`. -/
def Hnat (cfg : Config) : Nat := cfg.foldr (fun f acc => max (max (f.a + f.b) f.c) acc) 0
/-- The guaranteed threshold `M = H + 1`. -/
def Mval (cfg : Config) : Nat := Hnat cfg + 1

/-- Iterate the climb pump `k` times: `[n] → [n + k·g]`. -/
theorem reach_up_k {cfg : Config}
    (climb : ∀ n, Mval cfg ≤ n → Reach cfg [n] [n + gnat cfg]) (k : Nat) :
    ∀ n, Mval cfg ≤ n → Reach cfg [n] [n + k * gnat cfg] := by
  induction k with
  | zero => intro n _; simpa using Reach.refl [n]
  | succ k ih =>
    intro n hn
    have h1 := ih n hn
    have h2 := climb (n + k * gnat cfg) (Nat.le_trans hn (Nat.le_add_right _ _))
    have e : n + k * gnat cfg + gnat cfg = n + (k + 1) * gnat cfg := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [e] at h2
    exact reach_trans h1 h2

/-- Iterate the descend pump `k` times: `[n + k·g] → [n]`. -/
theorem reach_down_k {cfg : Config}
    (descend : ∀ n, Mval cfg ≤ n → Reach cfg [n + gnat cfg] [n]) (k : Nat) :
    ∀ n, Mval cfg ≤ n → Reach cfg [n + k * gnat cfg] [n] := by
  induction k with
  | zero => intro n _; simpa using Reach.refl [n]
  | succ k ih =>
    intro n hn
    have h2 := descend (n + k * gnat cfg) (Nat.le_trans hn (Nat.le_add_right _ _))
    have e : n + k * gnat cfg + gnat cfg = n + (k + 1) * gnat cfg := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [e] at h2
    exact reach_trans h2 (ih n hn)

/-- **Full sufficiency, reduced to the pumps.**  Given the one-step climb
    `[n] → [n+g]` and descend `[n+g] → [n]` for every `n ≥ M`, every pair `s,t ≥ M`
    with `g ∣ (t − s)` (the exact congruence of `reach_congr`) is solvable. -/
theorem sufficiency_of_pumps {cfg : Config}
    (climb : ∀ n, Mval cfg ≤ n → Reach cfg [n] [n + gnat cfg])
    (descend : ∀ n, Mval cfg ≤ n → Reach cfg [n + gnat cfg] [n])
    {s t : Nat} (hs : Mval cfg ≤ s) (ht : Mval cfg ≤ t)
    (hg : gz cfg ∣ ((t : Int) - s)) :
    Reach cfg [s] [t] := by
  have hg' : (gnat cfg : Int) ∣ ((t : Int) - s) := hg
  rcases Nat.le_total s t with hst | hst
  · have hc : ((t - s : Nat) : Int) = (t : Int) - s := by omega
    have hdvd : gnat cfg ∣ (t - s) := Int.natCast_dvd_natCast.1 (by rw [hc]; exact hg')
    obtain ⟨k, hk⟩ := hdvd
    have hk' : t - s = k * gnat cfg := by rw [Nat.mul_comm] at hk; exact hk
    have e : s + k * gnat cfg = t := by omega
    have hr := reach_up_k climb k s hs
    rwa [e] at hr
  · have hc : ((s - t : Nat) : Int) = (s : Int) - t := by omega
    have hg2 : (gnat cfg : Int) ∣ ((s : Int) - t) := by
      have h := dvd_neg' hg'
      have e2 : -((t : Int) - s) = (s : Int) - t := by omega
      rwa [e2] at h
    have hdvd : gnat cfg ∣ (s - t) := Int.natCast_dvd_natCast.1 (by rw [hc]; exact hg2)
    obtain ⟨k, hk⟩ := hdvd
    have hk' : s - t = k * gnat cfg := by rw [Nat.mul_comm] at hk; exact hk
    have e : t + k * gnat cfg = s := by omega
    have hr := reach_down_k descend k t ht
    rwa [e] at hr

end YaStupid

-- Trust check: these print the axiom dependencies (should be the standard
-- [propext, Classical.choice, Quot.sound] — and crucially NOT `sorryAx`).
#print axioms YaStupid.reach_congr
#print axioms YaStupid.classic_trap
#print axioms YaStupid.cfg222_5_to_7
#print axioms YaStupid.classic_21_to_19
#print axioms YaStupid.sufficiency_of_pumps
#print axioms YaStupid.classic_42_to_44
