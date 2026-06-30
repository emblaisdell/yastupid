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


theorem reach_frame {cfg : Config} {a b : List Nat} (r : List Nat) (h : Reach cfg a b) :
    Reach cfg (a ++ r) (b ++ r) := by
  induction h with
  | refl s => exact Reach.refl _
  | @step s t u hst hr ih =>
    obtain ⟨ain, aout, rest, hl, hps, hpt⟩ := hst
    have p1 : (s ++ r).Perm (ain ++ (rest ++ r)) := by
      have h2 := hps.append_right r; rwa [List.append_assoc] at h2
    have p2 : (t ++ r).Perm (aout ++ (rest ++ r)) := by
      have h2 := hpt.append_right r; rwa [List.append_assoc] at h2
    exact Reach.step ⟨ain, aout, rest ++ r, hl, p1, p2⟩ ih

theorem reach_frame_left {cfg : Config} {a b : List Nat} (r : List Nat) (h : Reach cfg a b) :
    Reach cfg (r ++ a) (r ++ b) := by
  induction h with
  | refl s => exact Reach.refl _
  | @step s t u hst hr ih =>
    obtain ⟨ain, aout, rest, hl, hps, hpt⟩ := hst
    have p1 : (r ++ s).Perm (ain ++ (r ++ rest)) := by
      have h2 := hps.append_left r
      have h3 : (r ++ (ain ++ rest)).Perm (ain ++ (r ++ rest)) := by
        rw [← List.append_assoc, ← List.append_assoc]; exact List.perm_append_comm.append_right rest
      exact h2.trans h3
    have p2 : (r ++ t).Perm (aout ++ (r ++ rest)) := by
      have h2 := hpt.append_left r
      have h3 : (r ++ (aout ++ rest)).Perm (aout ++ (r ++ rest)) := by
        rw [← List.append_assoc, ← List.append_assoc]; exact List.perm_append_comm.append_right rest
      exact h2.trans h3
    exact Reach.step ⟨ain, aout, r ++ rest, hl, p1, p2⟩ ih

theorem bc_22 : Reach classic [22] [24] :=
  reach_move [] (Local.nsplit 22 (by decide) (by decide)) (by decide) <|
  reach_move [11] (Local.nsplit 11 (by decide) (by decide)) (by decide) <|
  reach_move [6, 11] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [3, 11] (Local.nmerge 2 6 (by decide)) (by decide) <|
  reach_move [3] (Local.nmerge 8 11 (by decide)) (by decide) <|
  reach_move [3] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [3] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 3 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_23 : Reach classic [23] [25] :=
  reach_move [] (Local.nsplit 23 (by decide) (by decide)) (by decide) <|
  reach_move [12] (Local.nsplit 11 (by decide) (by decide)) (by decide) <|
  reach_move [6] (Local.nmerge 5 12 (by decide)) (by decide) <|
  reach_move [6] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [6, 9] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 9] (Local.nmerge 4 6 (by decide)) (by decide) <|
  reach_move [4] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 4 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_24 : Reach classic [24] [26] :=
  reach_move [] (Local.nsplit 24 (by decide) (by decide)) (by decide) <|
  reach_move [12] (Local.nsplit 12 (by decide) (by decide)) (by decide) <|
  reach_move [6] (Local.nmerge 6 12 (by decide)) (by decide) <|
  reach_move [6] (Local.nsplit 18 (by decide) (by decide)) (by decide) <|
  reach_move [6, 9] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [5, 9] (Local.nmerge 4 6 (by decide)) (by decide) <|
  reach_move [5] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 5 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_25 : Reach classic [25] [27] :=
  reach_move [] (Local.nsplit 25 (by decide) (by decide)) (by decide) <|
  reach_move [13] (Local.nsplit 12 (by decide) (by decide)) (by decide) <|
  reach_move [6] (Local.nmerge 6 13 (by decide)) (by decide) <|
  reach_move [6] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [6] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 6 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_26 : Reach classic [26] [28] :=
  reach_move [] (Local.nsplit 26 (by decide) (by decide)) (by decide) <|
  reach_move [13] (Local.nsplit 13 (by decide) (by decide)) (by decide) <|
  reach_move [7] (Local.nmerge 6 13 (by decide)) (by decide) <|
  reach_move [7] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [7] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 7 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_27 : Reach classic [27] [29] :=
  reach_move [] (Local.nsplit 27 (by decide) (by decide)) (by decide) <|
  reach_move [14] (Local.nsplit 13 (by decide) (by decide)) (by decide) <|
  reach_move [7, 14] (Local.nsplit 6 (by decide) (by decide)) (by decide) <|
  reach_move [3, 14] (Local.nmerge 3 7 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 3 14 (by decide)) (by decide) <|
  reach_move [10] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [8] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 8 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_28 : Reach classic [28] [30] :=
  reach_move [] (Local.nsplit 28 (by decide) (by decide)) (by decide) <|
  reach_move [14] (Local.nsplit 14 (by decide) (by decide)) (by decide) <|
  reach_move [7, 14] (Local.nsplit 7 (by decide) (by decide)) (by decide) <|
  reach_move [4, 14] (Local.nmerge 3 7 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 4 14 (by decide)) (by decide) <|
  reach_move [10] (Local.nsplit 18 (by decide) (by decide)) (by decide) <|
  reach_move [9] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 9 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_29 : Reach classic [29] [31] :=
  reach_move [] (Local.nsplit 29 (by decide) (by decide)) (by decide) <|
  reach_move [15] (Local.nsplit 14 (by decide) (by decide)) (by decide) <|
  reach_move [7, 15] (Local.nsplit 7 (by decide) (by decide)) (by decide) <|
  reach_move [4, 15] (Local.nmerge 3 7 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 4 15 (by decide)) (by decide) <|
  reach_move [10] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [10] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_30 : Reach classic [30] [32] :=
  reach_move [] (Local.nsplit 30 (by decide) (by decide)) (by decide) <|
  reach_move [15] (Local.nsplit 15 (by decide) (by decide)) (by decide) <|
  reach_move [8, 15] (Local.nsplit 7 (by decide) (by decide)) (by decide) <|
  reach_move [4, 15] (Local.nmerge 3 8 (by decide)) (by decide) <|
  reach_move [11] (Local.nmerge 4 15 (by decide)) (by decide) <|
  reach_move [11] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [11] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 11 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_31 : Reach classic [31] [33] :=
  reach_move [] (Local.nsplit 31 (by decide) (by decide)) (by decide) <|
  reach_move [16] (Local.nsplit 15 (by decide) (by decide)) (by decide) <|
  reach_move [8, 16] (Local.nsplit 7 (by decide) (by decide)) (by decide) <|
  reach_move [4, 8] (Local.nmerge 3 16 (by decide)) (by decide) <|
  reach_move [4, 8] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 4 8 (by decide)) (by decide) <|
  reach_move [12] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 12 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_32 : Reach classic [32] [34] :=
  reach_move [] (Local.nsplit 32 (by decide) (by decide)) (by decide) <|
  reach_move [16] (Local.nsplit 16 (by decide) (by decide)) (by decide) <|
  reach_move [8, 16] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 8, 16] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 4, 16] (Local.nmerge 2 8 (by decide)) (by decide) <|
  reach_move [4, 10] (Local.nmerge 2 16 (by decide)) (by decide) <|
  reach_move [4, 10] (Local.nsplit 18 (by decide) (by decide)) (by decide) <|
  reach_move [10, 9] (Local.nmerge 4 9 (by decide)) (by decide) <|
  reach_move [13] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 13 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_33 : Reach classic [33] [35] :=
  reach_move [] (Local.nsplit 33 (by decide) (by decide)) (by decide) <|
  reach_move [16] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [16, 9] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 9] (Local.nmerge 4 16 (by decide)) (by decide) <|
  reach_move [4, 9] (Local.nsplit 20 (by decide) (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 4 10 (by decide)) (by decide) <|
  reach_move [14] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 14 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_34 : Reach classic [34] [36] :=
  reach_move [] (Local.nsplit 34 (by decide) (by decide)) (by decide) <|
  reach_move [17] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [9, 17] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 9, 17] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 2, 4, 9] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 8, 9] (Local.nmerge 2 4 (by decide)) (by decide) <|
  reach_move [9, 9, 6] (Local.nmerge 2 8 (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 6 9 (by decide)) (by decide) <|
  reach_move [15] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 15 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_35 : Reach classic [35] [37] :=
  reach_move [] (Local.nsplit 35 (by decide) (by decide)) (by decide) <|
  reach_move [18] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [9, 18] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 9, 18] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 18] (Local.nmerge 2 4 (by decide)) (by decide) <|
  reach_move [9, 6] (Local.nmerge 2 18 (by decide)) (by decide) <|
  reach_move [9, 6] (Local.nsplit 20 (by decide) (by decide)) (by decide) <|
  reach_move [6, 10] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [21] (Local.nmerge 6 10 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 16 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_36 : Reach classic [36] [38] :=
  reach_move [] (Local.nsplit 36 (by decide) (by decide)) (by decide) <|
  reach_move [18] (Local.nsplit 18 (by decide) (by decide)) (by decide) <|
  reach_move [9, 18] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [5, 9, 18] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 18] (Local.nmerge 2 5 (by decide)) (by decide) <|
  reach_move [9, 7] (Local.nmerge 2 18 (by decide)) (by decide) <|
  reach_move [9, 7] (Local.nsplit 20 (by decide) (by decide)) (by decide) <|
  reach_move [7, 10] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [21] (Local.nmerge 7 10 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 17 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_37 : Reach classic [37] [39] :=
  reach_move [] (Local.nsplit 37 (by decide) (by decide)) (by decide) <|
  reach_move [18] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [18] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 18 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_38 : Reach classic [38] [40] :=
  reach_move [] (Local.nsplit 38 (by decide) (by decide)) (by decide) <|
  reach_move [19] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [19] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 19 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_39 : Reach classic [39] [41] :=
  reach_move [] (Local.nsplit 39 (by decide) (by decide)) (by decide) <|
  reach_move [20] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [20] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 20 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_40 : Reach classic [40] [42] :=
  reach_move [] (Local.nsplit 40 (by decide) (by decide)) (by decide) <|
  reach_move [20] (Local.nsplit 20 (by decide) (by decide)) (by decide) <|
  reach_move [10, 20] (Local.nsplit 10 (by decide) (by decide)) (by decide) <|
  reach_move [5, 10, 20] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [3, 5, 10, 20] (Local.nsplit 2 (by decide) (by decide)) (by decide) <|
  reach_move [1, 5, 10, 20] (Local.nmerge 1 3 (by decide)) (by decide) <|
  reach_move [5, 10, 4] (Local.nmerge 1 20 (by decide)) (by decide) <|
  reach_move [10, 21] (Local.nmerge 4 5 (by decide)) (by decide) <|
  reach_move [21] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 21 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_41 : Reach classic [41] [43] :=
  reach_move [] (Local.nsplit 41 (by decide) (by decide)) (by decide) <|
  reach_move [21] (Local.nsplit 20 (by decide) (by decide)) (by decide) <|
  reach_move [10, 21] (Local.nsplit 10 (by decide) (by decide)) (by decide) <|
  reach_move [5, 10, 21] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [3, 5, 10, 21] (Local.nsplit 2 (by decide) (by decide)) (by decide) <|
  reach_move [1, 5, 10, 21] (Local.nmerge 1 3 (by decide)) (by decide) <|
  reach_move [5, 10, 4] (Local.nmerge 1 21 (by decide)) (by decide) <|
  reach_move [10, 22] (Local.nmerge 4 5 (by decide)) (by decide) <|
  reach_move [22] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 21 22 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_42 : Reach classic [42] [44] :=
  reach_move [] (Local.nsplit 42 (by decide) (by decide)) (by decide) <|
  reach_move [21] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10, 21] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [5, 10, 21] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 10, 21] (Local.nmerge 2 5 (by decide)) (by decide) <|
  reach_move [2, 7] (Local.nmerge 10 21 (by decide)) (by decide) <|
  reach_move [2] (Local.nmerge 7 31 (by decide)) (by decide) <|
  reach_move [2] (Local.nsplit 38 (by decide) (by decide)) (by decide) <|
  reach_move [2, 19] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 10] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 10] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 2 21 (by decide)) (by decide) <|
  reach_move [23] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 21 23 (by decide)) (by decide) <|
  Reach.refl _

theorem bc_43 : Reach classic [43] [45] :=
  reach_move [] (Local.nsplit 43 (by decide) (by decide)) (by decide) <|
  reach_move [21] (Local.nsplit 22 (by decide) (by decide)) (by decide) <|
  reach_move [21, 11] (Local.nsplit 11 (by decide) (by decide)) (by decide) <|
  reach_move [21, 6, 11] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [2, 6, 11] (Local.nmerge 3 21 (by decide)) (by decide) <|
  reach_move [11, 24] (Local.nmerge 2 6 (by decide)) (by decide) <|
  reach_move [24] (Local.nmerge 8 11 (by decide)) (by decide) <|
  reach_move [24] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [24] (Local.fmerge ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 21 24 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_24 : Reach classic [24] [22] :=
  reach_move [] (Local.nsplit 24 (by decide) (by decide)) (by decide) <|
  reach_move [12] (Local.nsplit 12 (by decide) (by decide)) (by decide) <|
  reach_move [6, 12] (Local.nsplit 6 (by decide) (by decide)) (by decide) <|
  reach_move [3, 12] (Local.nmerge 3 6 (by decide)) (by decide) <|
  reach_move [3] (Local.nmerge 9 12 (by decide)) (by decide) <|
  reach_move [3] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 3 9 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 12 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_25 : Reach classic [25] [23] :=
  reach_move [] (Local.nsplit 25 (by decide) (by decide)) (by decide) <|
  reach_move [12] (Local.nsplit 13 (by decide) (by decide)) (by decide) <|
  reach_move [12, 6] (Local.nsplit 7 (by decide) (by decide)) (by decide) <|
  reach_move [3, 4] (Local.nmerge 6 12 (by decide)) (by decide) <|
  reach_move [4] (Local.nmerge 3 18 (by decide)) (by decide) <|
  reach_move [4] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 4 9 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 13 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_26 : Reach classic [26] [24] :=
  reach_move [] (Local.nsplit 26 (by decide) (by decide)) (by decide) <|
  reach_move [13] (Local.nsplit 13 (by decide) (by decide)) (by decide) <|
  reach_move [7, 13] (Local.nsplit 6 (by decide) (by decide)) (by decide) <|
  reach_move [3, 7, 13] (Local.nsplit 3 (by decide) (by decide)) (by decide) <|
  reach_move [2, 3, 13] (Local.nmerge 1 7 (by decide)) (by decide) <|
  reach_move [13, 8] (Local.nmerge 2 3 (by decide)) (by decide) <|
  reach_move [5] (Local.nmerge 8 13 (by decide)) (by decide) <|
  reach_move [5] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 5 9 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 14 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_27 : Reach classic [27] [25] :=
  reach_move [] (Local.nsplit 27 (by decide) (by decide)) (by decide) <|
  reach_move [14] (Local.nsplit 13 (by decide) (by decide)) (by decide) <|
  reach_move [6] (Local.nmerge 7 14 (by decide)) (by decide) <|
  reach_move [6] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 6 9 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 15 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_28 : Reach classic [28] [26] :=
  reach_move [] (Local.nsplit 28 (by decide) (by decide)) (by decide) <|
  reach_move [14] (Local.nsplit 14 (by decide) (by decide)) (by decide) <|
  reach_move [7] (Local.nmerge 7 14 (by decide)) (by decide) <|
  reach_move [7] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 7 9 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 16 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_29 : Reach classic [29] [27] :=
  reach_move [] (Local.nsplit 29 (by decide) (by decide)) (by decide) <|
  reach_move [14] (Local.nsplit 15 (by decide) (by decide)) (by decide) <|
  reach_move [8] (Local.nmerge 7 14 (by decide)) (by decide) <|
  reach_move [8] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 8 9 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 17 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_30 : Reach classic [30] [28] :=
  reach_move [] (Local.nsplit 30 (by decide) (by decide)) (by decide) <|
  reach_move [15] (Local.nsplit 15 (by decide) (by decide)) (by decide) <|
  reach_move [8, 15] (Local.nsplit 7 (by decide) (by decide)) (by decide) <|
  reach_move [4, 8, 15] (Local.nsplit 3 (by decide) (by decide)) (by decide) <|
  reach_move [2, 4, 15] (Local.nmerge 1 8 (by decide)) (by decide) <|
  reach_move [15, 9] (Local.nmerge 2 4 (by decide)) (by decide) <|
  reach_move [9] (Local.nmerge 6 15 (by decide)) (by decide) <|
  reach_move [9] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 9 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 18 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_31 : Reach classic [31] [29] :=
  reach_move [] (Local.nsplit 31 (by decide) (by decide)) (by decide) <|
  reach_move [16] (Local.nsplit 15 (by decide) (by decide)) (by decide) <|
  reach_move [8, 16] (Local.nsplit 7 (by decide) (by decide)) (by decide) <|
  reach_move [4, 8, 16] (Local.nsplit 3 (by decide) (by decide)) (by decide) <|
  reach_move [2, 8, 16] (Local.nmerge 1 4 (by decide)) (by decide) <|
  reach_move [16, 5] (Local.nmerge 2 8 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 5 16 (by decide)) (by decide) <|
  reach_move [10] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [9] (Local.nmerge 10 10 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 9 20 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_32 : Reach classic [32] [30] :=
  reach_move [] (Local.nsplit 32 (by decide) (by decide)) (by decide) <|
  reach_move [16] (Local.nsplit 16 (by decide) (by decide)) (by decide) <|
  reach_move [8, 16] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 8, 16] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 4, 8, 16] (Local.nsplit 2 (by decide) (by decide)) (by decide) <|
  reach_move [1, 4, 8, 16] (Local.nmerge 1 2 (by decide)) (by decide) <|
  reach_move [8, 16, 3] (Local.nmerge 1 4 (by decide)) (by decide) <|
  reach_move [16, 5] (Local.nmerge 3 8 (by decide)) (by decide) <|
  reach_move [11] (Local.nmerge 5 16 (by decide)) (by decide) <|
  reach_move [11] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 11 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 20 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_33 : Reach classic [33] [31] :=
  reach_move [] (Local.nsplit 33 (by decide) (by decide)) (by decide) <|
  reach_move [17] (Local.nsplit 16 (by decide) (by decide)) (by decide) <|
  reach_move [8, 17] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 17] (Local.nmerge 4 8 (by decide)) (by decide) <|
  reach_move [12] (Local.nmerge 4 17 (by decide)) (by decide) <|
  reach_move [12] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 12 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 21 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_34 : Reach classic [34] [32] :=
  reach_move [] (Local.nsplit 34 (by decide) (by decide)) (by decide) <|
  reach_move [17] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [9, 17] (Local.nsplit 8 (by decide) (by decide)) (by decide) <|
  reach_move [4, 17] (Local.nmerge 4 9 (by decide)) (by decide) <|
  reach_move [13] (Local.nmerge 4 17 (by decide)) (by decide) <|
  reach_move [13] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 13 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 22 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_35 : Reach classic [35] [33] :=
  reach_move [] (Local.nsplit 35 (by decide) (by decide)) (by decide) <|
  reach_move [18] (Local.nsplit 17 (by decide) (by decide)) (by decide) <|
  reach_move [8] (Local.nmerge 9 18 (by decide)) (by decide) <|
  reach_move [8] (Local.nsplit 27 (by decide) (by decide)) (by decide) <|
  reach_move [14] (Local.nmerge 8 13 (by decide)) (by decide) <|
  reach_move [14] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 14 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 23 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_36 : Reach classic [36] [34] :=
  reach_move [] (Local.nsplit 36 (by decide) (by decide)) (by decide) <|
  reach_move [18] (Local.nsplit 18 (by decide) (by decide)) (by decide) <|
  reach_move [9, 18] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [4, 9, 18] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [3, 9, 18] (Local.nmerge 2 4 (by decide)) (by decide) <|
  reach_move [9, 6] (Local.nmerge 3 18 (by decide)) (by decide) <|
  reach_move [9, 6] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 6 9 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 15 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 24 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_37 : Reach classic [37] [35] :=
  reach_move [] (Local.nsplit 37 (by decide) (by decide)) (by decide) <|
  reach_move [19] (Local.nsplit 18 (by decide) (by decide)) (by decide) <|
  reach_move [9, 19] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [5, 9, 19] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 9, 19] (Local.nmerge 2 5 (by decide)) (by decide) <|
  reach_move [9, 7] (Local.nmerge 2 19 (by decide)) (by decide) <|
  reach_move [9, 7] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 7 9 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 16 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 25 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_38 : Reach classic [38] [36] :=
  reach_move [] (Local.nsplit 38 (by decide) (by decide)) (by decide) <|
  reach_move [19] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [10, 19] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [5, 10, 19] (Local.nsplit 4 (by decide) (by decide)) (by decide) <|
  reach_move [2, 10, 19] (Local.nmerge 2 5 (by decide)) (by decide) <|
  reach_move [10, 7] (Local.nmerge 2 19 (by decide)) (by decide) <|
  reach_move [10, 7] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 7 10 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 17 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 26 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_39 : Reach classic [39] [37] :=
  reach_move [] (Local.nsplit 39 (by decide) (by decide)) (by decide) <|
  reach_move [20] (Local.nsplit 19 (by decide) (by decide)) (by decide) <|
  reach_move [10, 20] (Local.nsplit 9 (by decide) (by decide)) (by decide) <|
  reach_move [4, 20] (Local.nmerge 5 10 (by decide)) (by decide) <|
  reach_move [4] (Local.nmerge 15 20 (by decide)) (by decide) <|
  reach_move [4] (Local.nsplit 35 (by decide) (by decide)) (by decide) <|
  reach_move [18] (Local.nmerge 4 17 (by decide)) (by decide) <|
  reach_move [18] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 18 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 27 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_40 : Reach classic [40] [38] :=
  reach_move [] (Local.nsplit 40 (by decide) (by decide)) (by decide) <|
  reach_move [20] (Local.nsplit 20 (by decide) (by decide)) (by decide) <|
  reach_move [10, 20] (Local.nsplit 10 (by decide) (by decide)) (by decide) <|
  reach_move [5, 10, 20] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [3, 5, 10, 20] (Local.nsplit 2 (by decide) (by decide)) (by decide) <|
  reach_move [1, 5, 10, 20] (Local.nmerge 1 3 (by decide)) (by decide) <|
  reach_move [5, 10, 4] (Local.nmerge 1 20 (by decide)) (by decide) <|
  reach_move [5, 10, 4] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [4, 9, 10] (Local.nmerge 5 10 (by decide)) (by decide) <|
  reach_move [10, 15] (Local.nmerge 4 9 (by decide)) (by decide) <|
  reach_move [13] (Local.nmerge 10 15 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 13 25 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_41 : Reach classic [41] [39] :=
  reach_move [] (Local.nsplit 41 (by decide) (by decide)) (by decide) <|
  reach_move [20] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 20 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 29 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_42 : Reach classic [42] [40] :=
  reach_move [] (Local.nsplit 42 (by decide) (by decide)) (by decide) <|
  reach_move [21] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 21 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 30 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_43 : Reach classic [43] [41] :=
  reach_move [] (Local.nsplit 43 (by decide) (by decide)) (by decide) <|
  reach_move [22] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 22 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 31 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_44 : Reach classic [44] [42] :=
  reach_move [] (Local.nsplit 44 (by decide) (by decide)) (by decide) <|
  reach_move [22] (Local.nsplit 22 (by decide) (by decide)) (by decide) <|
  reach_move [11, 22] (Local.nsplit 11 (by decide) (by decide)) (by decide) <|
  reach_move [5, 6] (Local.nmerge 11 22 (by decide)) (by decide) <|
  reach_move [5, 6] (Local.nsplit 33 (by decide) (by decide)) (by decide) <|
  reach_move [6, 17] (Local.nmerge 5 16 (by decide)) (by decide) <|
  reach_move [6, 17] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [9, 10] (Local.nmerge 6 17 (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 23 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 32 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_45 : Reach classic [45] [43] :=
  reach_move [] (Local.nsplit 45 (by decide) (by decide)) (by decide) <|
  reach_move [22] (Local.nsplit 23 (by decide) (by decide)) (by decide) <|
  reach_move [22, 12] (Local.nsplit 11 (by decide) (by decide)) (by decide) <|
  reach_move [22, 6, 12] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [3, 6, 12] (Local.nmerge 2 22 (by decide)) (by decide) <|
  reach_move [12, 24] (Local.nmerge 3 6 (by decide)) (by decide) <|
  reach_move [24] (Local.nmerge 9 12 (by decide)) (by decide) <|
  reach_move [24] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 24 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 33 (by decide)) (by decide) <|
  Reach.refl _

theorem bd_46 : Reach classic [46] [44] :=
  reach_move [] (Local.nsplit 46 (by decide) (by decide)) (by decide) <|
  reach_move [23] (Local.nsplit 23 (by decide) (by decide)) (by decide) <|
  reach_move [12, 23] (Local.nsplit 11 (by decide) (by decide)) (by decide) <|
  reach_move [6, 12, 23] (Local.nsplit 5 (by decide) (by decide)) (by decide) <|
  reach_move [3, 6, 12] (Local.nmerge 2 23 (by decide)) (by decide) <|
  reach_move [12, 25] (Local.nmerge 3 6 (by decide)) (by decide) <|
  reach_move [25] (Local.nmerge 9 12 (by decide)) (by decide) <|
  reach_move [25] (Local.fsplit ⟨9, 10, 21⟩ (by decide)) (by decide) <|
  reach_move [10] (Local.nmerge 9 25 (by decide)) (by decide) <|
  reach_move [] (Local.nmerge 10 34 (by decide)) (by decide) <|
  Reach.refl _

def baseClimb : (n : Nat) → 22 ≤ n → n ≤ 43 → Reach classic [n] [n + 2]
  | 22, _, _ => bc_22
  | 23, _, _ => bc_23
  | 24, _, _ => bc_24
  | 25, _, _ => bc_25
  | 26, _, _ => bc_26
  | 27, _, _ => bc_27
  | 28, _, _ => bc_28
  | 29, _, _ => bc_29
  | 30, _, _ => bc_30
  | 31, _, _ => bc_31
  | 32, _, _ => bc_32
  | 33, _, _ => bc_33
  | 34, _, _ => bc_34
  | 35, _, _ => bc_35
  | 36, _, _ => bc_36
  | 37, _, _ => bc_37
  | 38, _, _ => bc_38
  | 39, _, _ => bc_39
  | 40, _, _ => bc_40
  | 41, _, _ => bc_41
  | 42, _, _ => bc_42
  | 43, _, _ => bc_43
  | 0, hn, _ => absurd hn (by decide)
  | 1, hn, _ => absurd hn (by decide)
  | 2, hn, _ => absurd hn (by decide)
  | 3, hn, _ => absurd hn (by decide)
  | 4, hn, _ => absurd hn (by decide)
  | 5, hn, _ => absurd hn (by decide)
  | 6, hn, _ => absurd hn (by decide)
  | 7, hn, _ => absurd hn (by decide)
  | 8, hn, _ => absurd hn (by decide)
  | 9, hn, _ => absurd hn (by decide)
  | 10, hn, _ => absurd hn (by decide)
  | 11, hn, _ => absurd hn (by decide)
  | 12, hn, _ => absurd hn (by decide)
  | 13, hn, _ => absurd hn (by decide)
  | 14, hn, _ => absurd hn (by decide)
  | 15, hn, _ => absurd hn (by decide)
  | 16, hn, _ => absurd hn (by decide)
  | 17, hn, _ => absurd hn (by decide)
  | 18, hn, _ => absurd hn (by decide)
  | 19, hn, _ => absurd hn (by decide)
  | 20, hn, _ => absurd hn (by decide)
  | 21, hn, _ => absurd hn (by decide)
  | (n+44), _, hb => absurd hb (by omega)

def baseDesc : (m : Nat) → 24 ≤ m → m ≤ 46 → Reach classic [m] [m - 2]
  | 24, _, _ => bd_24
  | 25, _, _ => bd_25
  | 26, _, _ => bd_26
  | 27, _, _ => bd_27
  | 28, _, _ => bd_28
  | 29, _, _ => bd_29
  | 30, _, _ => bd_30
  | 31, _, _ => bd_31
  | 32, _, _ => bd_32
  | 33, _, _ => bd_33
  | 34, _, _ => bd_34
  | 35, _, _ => bd_35
  | 36, _, _ => bd_36
  | 37, _, _ => bd_37
  | 38, _, _ => bd_38
  | 39, _, _ => bd_39
  | 40, _, _ => bd_40
  | 41, _, _ => bd_41
  | 42, _, _ => bd_42
  | 43, _, _ => bd_43
  | 44, _, _ => bd_44
  | 45, _, _ => bd_45
  | 46, _, _ => bd_46
  | 0, hn, _ => absurd hn (by decide)
  | 1, hn, _ => absurd hn (by decide)
  | 2, hn, _ => absurd hn (by decide)
  | 3, hn, _ => absurd hn (by decide)
  | 4, hn, _ => absurd hn (by decide)
  | 5, hn, _ => absurd hn (by decide)
  | 6, hn, _ => absurd hn (by decide)
  | 7, hn, _ => absurd hn (by decide)
  | 8, hn, _ => absurd hn (by decide)
  | 9, hn, _ => absurd hn (by decide)
  | 10, hn, _ => absurd hn (by decide)
  | 11, hn, _ => absurd hn (by decide)
  | 12, hn, _ => absurd hn (by decide)
  | 13, hn, _ => absurd hn (by decide)
  | 14, hn, _ => absurd hn (by decide)
  | 15, hn, _ => absurd hn (by decide)
  | 16, hn, _ => absurd hn (by decide)
  | 17, hn, _ => absurd hn (by decide)
  | 18, hn, _ => absurd hn (by decide)
  | 19, hn, _ => absurd hn (by decide)
  | 20, hn, _ => absurd hn (by decide)
  | 21, hn, _ => absurd hn (by decide)
  | 22, hn, _ => absurd hn (by decide)
  | 23, hn, _ => absurd hn (by decide)
  | (n+47), _, hb => absurd hb (by omega)

theorem climb_all (base : ∀ n, 22 ≤ n → n ≤ 43 → Reach classic [n] [n + 2]) :
    ∀ n, 22 ≤ n → Reach classic [n] [n + 2] := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hb : n ≤ 43
    · exact base n hn hb
    · have h44 : 44 ≤ n := by omega
      have hcl : Reach classic [(n+1)/2] [(n+1)/2 + 2] := ih ((n+1)/2) (by omega) (by omega)
      have hsp : Reach classic [n] [n/2, (n+1)/2] :=
        reach_move [] (Local.nsplit n (by omega)
          (by simp only [classic, List.mem_singleton, forall_eq]; omega))
          (List.Perm.refl _) (Reach.refl _)
      have hfr : Reach classic ([n/2] ++ [(n+1)/2]) ([n/2] ++ [(n+1)/2 + 2]) :=
        reach_frame_left [n/2] hcl
      have hmg : Reach classic [n/2, (n+1)/2 + 2] [n + 2] := by
        have hc : ∀ f ∈ classic, ¬ ((f.a = n/2 ∧ f.b = (n+1)/2 + 2) ∨ (f.a = (n+1)/2 + 2 ∧ f.b = n/2)) := by
          simp only [classic, List.mem_singleton, forall_eq]; omega
        have hm := reach_move [] (Local.nmerge (n/2) ((n+1)/2 + 2) hc) (List.Perm.refl _) (Reach.refl _)
        have e : n/2 + ((n+1)/2 + 2) = n + 2 := by omega
        rwa [e] at hm
      exact reach_trans hsp (reach_trans hfr hmg)

theorem descD (base : ∀ m, 24 ≤ m → m ≤ 46 → Reach classic [m] [m - 2]) :
    ∀ m, 24 ≤ m → Reach classic [m] [m - 2] := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    by_cases hb : m ≤ 46
    · exact base m hm hb
    · have h47 : 47 ≤ m := by omega
      have hcl : Reach classic [(m+1)/2] [(m+1)/2 - 2] := ih ((m+1)/2) (by omega) (by omega)
      have hsp : Reach classic [m] [m/2, (m+1)/2] :=
        reach_move [] (Local.nsplit m (by omega)
          (by simp only [classic, List.mem_singleton, forall_eq]; omega))
          (List.Perm.refl _) (Reach.refl _)
      have hfr : Reach classic ([m/2] ++ [(m+1)/2]) ([m/2] ++ [(m+1)/2 - 2]) :=
        reach_frame_left [m/2] hcl
      have hmg : Reach classic [m/2, (m+1)/2 - 2] [m - 2] := by
        have hc : ∀ f ∈ classic, ¬ ((f.a = m/2 ∧ f.b = (m+1)/2 - 2) ∨ (f.a = (m+1)/2 - 2 ∧ f.b = m/2)) := by
          simp only [classic, List.mem_singleton, forall_eq]; omega
        have hm2 := reach_move [] (Local.nmerge (m/2) ((m+1)/2 - 2) hc) (List.Perm.refl _) (Reach.refl _)
        have e : m/2 + ((m+1)/2 - 2) = m - 2 := by omega
        rwa [e] at hm2
      exact reach_trans hsp (reach_trans hfr hmg)

/-- **Full sufficiency for Classic mode** (`9 + 10 = 21`).  Every `s, t ≥ 22` with
    `t ≡ s (mod 2)` is solvable.  No `sorry`. -/
theorem classic_sufficiency {s t : Nat} (hs : 22 ≤ s) (ht : 22 ≤ t)
    (hg : (2 : Int) ∣ ((t : Int) - s)) : Reach classic [s] [t] := by
  have hMc : Mval classic = 22 := by decide
  have hgnc : gnat classic = 2 := by decide
  have hclimb : ∀ n, Mval classic ≤ n → Reach classic [n] [n + gnat classic] := by
    intro n hn; rw [hgnc]; exact climb_all baseClimb n (by rw [hMc] at hn; exact hn)
  have hdescend : ∀ n, Mval classic ≤ n → Reach classic [n + gnat classic] [n] := by
    intro n hn; rw [hgnc]
    have hd : Reach classic [n + 2] [(n + 2) - 2] := descD baseDesc (n + 2) (by rw [hMc] at hn; omega)
    have e : (n + 2) - 2 = n := by omega
    rwa [e] at hd
  have hgz : gz classic ∣ ((t : Int) - s) := by
    have h2 : gz classic = 2 := by decide
    rw [h2]; exact hg
  exact sufficiency_of_pumps hclimb hdescend (by rw [hMc]; exact hs) (by rw [hMc]; exact ht) hgz

/-! ### Toward the symbolic single-sum theorem

For an *arbitrary* single false sum `[⟨a,b,c⟩]` (`a+b ≠ c`), the framing rule plus a
halving recursion reduce the two pumps to a bounded base interval, and the general
`sufficiency_of_pumps` then yields full sufficiency.  All `sorry`-free. -/

/-- Building block for the (still open) base carve: merge `k` ones into a single
    ball `[k]`.  Safe — never forms the forbidden pair `{a,b}` — whenever
    `k ≤ max a b`, which covers every value we need to build (`a` and `b`).
    Its dual, *scatter* (peeling units out of a ball), is the remaining obstacle:
    it must escape the locked value `c` inside the recursion and handle the
    `c·2^k` stuck values, which cannot be scattered sum-preservingly. -/
theorem gather (a b c : Nat) :
    ∀ k, 1 ≤ k → k ≤ max a b → Reach [⟨a,b,c⟩] (List.replicate k 1) [k] := by
  intro k
  induction k with
  | zero => intro h _; omega
  | succ k ih =>
    intro _ hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; exact Reach.refl _
    · have prev := ih hkpos (by omega)
      have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config),
          ¬ ((f.a = 1 ∧ f.b = k) ∨ (f.a = k ∧ f.b = 1)) := by
        simp only [List.mem_singleton, forall_eq]; omega
      have step2 : Reach [⟨a,b,c⟩] [1, k] [k + 1] := by
        have hm := reach_move [] (Local.nmerge 1 k hcc) (List.Perm.refl _) (Reach.refl _)
        have e : 1 + k = k + 1 := by omega
        rwa [e] at hm
      exact reach_trans (reach_frame_left [1] prev) step2

theorem climb_of_base (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hne : a + b ≠ c)
    (base : ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]]) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]] := by
  have hHab : a + b ≤ Hnat [⟨a,b,c⟩] := by show a + b ≤ max (max (a+b) c) 0; omega
  have hHc  : c ≤ Hnat [⟨a,b,c⟩] := by show c ≤ max (max (a+b) c) 0; omega
  have hMdef : Mval [⟨a,b,c⟩] = Hnat [⟨a,b,c⟩] + 1 := rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hbase : n ≤ 2 * Hnat [⟨a,b,c⟩]
    · exact base n hn hbase
    · have hH2 : 2 * Hnat [⟨a,b,c⟩] < n := by omega
      have hMle : Mval [⟨a,b,c⟩] ≤ (n+1)/2 := by omega
      have hlt : (n+1)/2 < n := by omega
      have hcl := ih ((n+1)/2) hlt hMle
      have hsp : Reach [⟨a,b,c⟩] [n] [n/2, (n+1)/2] :=
        reach_move [] (Local.nsplit n (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega))
          (List.Perm.refl _) (Reach.refl _)
      have hfr := reach_frame_left [n/2] hcl
      have hmg : Reach [⟨a,b,c⟩] [n/2, (n+1)/2 + gnat [⟨a,b,c⟩]] [n + gnat [⟨a,b,c⟩]] := by
        have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config),
            ¬ ((f.a = n/2 ∧ f.b = (n+1)/2 + gnat [⟨a,b,c⟩]) ∨
               (f.a = (n+1)/2 + gnat [⟨a,b,c⟩] ∧ f.b = n/2)) := by
          simp only [List.mem_singleton, forall_eq]; omega
        have hm := reach_move [] (Local.nmerge (n/2) ((n+1)/2 + gnat [⟨a,b,c⟩]) hcc)
          (List.Perm.refl _) (Reach.refl _)
        have e : n/2 + ((n+1)/2 + gnat [⟨a,b,c⟩]) = n + gnat [⟨a,b,c⟩] := by omega
        rwa [e] at hm
      exact reach_trans hsp (reach_trans hfr hmg)


theorem descend_of_base (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hne : a + b ≠ c)
    (base : ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n]) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n] := by
  have hHab : a + b ≤ Hnat [⟨a,b,c⟩] := by show a + b ≤ max (max (a+b) c) 0; omega
  have hHc  : c ≤ Hnat [⟨a,b,c⟩] := by show c ≤ max (max (a+b) c) 0; omega
  have hMdef : Mval [⟨a,b,c⟩] = Hnat [⟨a,b,c⟩] + 1 := rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hbase : n ≤ 2 * Hnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩]
    · exact base n hn hbase
    · have hH2 : 2 * Hnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩] < n := by omega
      have hsp : Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]]
                 [(n + gnat [⟨a,b,c⟩])/2, (n + gnat [⟨a,b,c⟩] + 1)/2] :=
        reach_move [] (Local.nsplit (n + gnat [⟨a,b,c⟩]) (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega))
          (List.Perm.refl _) (Reach.refl _)
      have hk : (n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩]
                = (n + gnat [⟨a,b,c⟩] + 1)/2 := by omega
      have hMle : Mval [⟨a,b,c⟩] ≤ (n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩] := by omega
      have hlt : (n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩] < n := by omega
      have hcl0 := ih ((n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩]) hlt hMle
      rw [hk] at hcl0
      have hfr := reach_frame_left [(n + gnat [⟨a,b,c⟩])/2] hcl0
      have hmg : Reach [⟨a,b,c⟩]
          [(n + gnat [⟨a,b,c⟩])/2, (n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩]] [n] := by
        have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config),
            ¬ ((f.a = (n + gnat [⟨a,b,c⟩])/2 ∧
                  f.b = (n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩]) ∨
               (f.a = (n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩] ∧
                  f.b = (n + gnat [⟨a,b,c⟩])/2)) := by
          simp only [List.mem_singleton, forall_eq]; omega
        have hm := reach_move [] (Local.nmerge ((n + gnat [⟨a,b,c⟩])/2)
          ((n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩]) hcc) (List.Perm.refl _) (Reach.refl _)
        have e : (n + gnat [⟨a,b,c⟩])/2 + ((n + gnat [⟨a,b,c⟩] + 1)/2 - gnat [⟨a,b,c⟩]) = n := by omega
        rwa [e] at hm
      exact reach_trans hsp (reach_trans hfr hmg)

/-- **Symbolic sufficiency, reduced to base cases.**  For *any* single false sum
    `{a,b,c}` (a+b ≠ c), if the climb/descend pumps hold on the bounded base
    interval, then full sufficiency holds: every `s,t ≥ M` with `g ∣ (t−s)`. -/
theorem single_sufficiency_of_base (a b c : Nat)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hne : a + b ≠ c)
    (baseC : ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]])
    (baseD : ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n]) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  fun s t hs ht hg =>
    sufficiency_of_pumps (climb_of_base a b c ha hb hc hne baseC)
      (descend_of_base a b c ha hb hc hne baseD) hs ht hg



theorem replicate_one_add (p q : Nat) :
    List.replicate p (1:Nat) ++ List.replicate q 1 = List.replicate (p+q) 1 := by
  induction p with
  | zero => simp
  | succ p ih => simp [List.replicate_succ, ih, Nat.succ_add]

theorem scatterClean (a b c : Nat) :
    ∀ n, 1 ≤ n → n < c → Reach [⟨a,b,c⟩] [n] (List.replicate n 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn1 hnc
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn : n = 1 := by omega
      subst hn; exact Reach.refl _
    · have hsplit : Reach [⟨a,b,c⟩] [n] [n/2, (n+1)/2] :=
        reach_move [] (Local.nsplit n (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
      have hsc1 := ih (n/2) (by omega) (by omega) (by omega)
      have hsc2 := ih ((n+1)/2) (by omega) (by omega) (by omega)
      have step1 := reach_frame [(n+1)/2] hsc1
      have step2 := reach_frame_left (List.replicate (n/2) 1) hsc2
      have hcat : List.replicate (n/2) 1 ++ List.replicate ((n+1)/2) 1 = List.replicate n 1 := by
        rw [replicate_one_add]; congr 1; omega
      rw [hcat] at step2
      exact reach_trans hsplit (reach_trans step1 step2)


/-- For the clean part of the base (`n ≤ 2c-2`, so both halves are `< c`),
    scatter `[n]` to all-ones. -/
theorem getUnits (a b c : Nat) :
    ∀ n, c + 1 ≤ n → n ≤ 2*c - 2 → Reach [⟨a,b,c⟩] [n] (List.replicate n 1) := by
  intro n h1 h2
  have hsplit : Reach [⟨a,b,c⟩] [n] [n/2, (n+1)/2] :=
    reach_move [] (Local.nsplit n (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hsc1 := scatterClean a b c (n/2) (by omega) (by omega)
  have hsc2 := scatterClean a b c ((n+1)/2) (by omega) (by omega)
  have step1 := reach_frame [(n+1)/2] hsc1
  have step2 := reach_frame_left (List.replicate (n/2) 1) hsc2
  have hcat : List.replicate (n/2) 1 ++ List.replicate ((n+1)/2) 1 = List.replicate n 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [hcat] at step2
  exact reach_trans hsplit (reach_trans step1 step2)

/-- Gather `k` ones onto a ball `v` with `v > max a b` (so every intermediate
    `v+i` is above both `a` and `b`, never forming the forbidden pair). -/
theorem mergeUnitsHi (a b c : Nat) :
    ∀ k v, max a b < v → Reach [⟨a,b,c⟩] (v :: List.replicate k 1) [v + k] := by
  intro k
  induction k with
  | zero => intro v _; exact Reach.refl _
  | succ k ih =>
    intro v hv
    have hc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = v ∧ f.b = 1) ∨ (f.a = 1 ∧ f.b = v)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move (List.replicate k 1) (Local.nmerge v 1 hc) (List.Perm.refl _) (Reach.refl _)
    have hrec := ih (v+1) (by omega)
    have e : (v+1) + k = v + (k+1) := by omega
    rw [e] at hrec
    exact reach_trans hm hrec


/-! ### Toward an unconditional base for the `d < 0` case (`a + b < c`)

When `a + b < c`, the inaccuracy is `g = c - a - b` and `c > max a b`, so the
false sum's right-hand side `c` is strictly above both legs.  We discharge the
climb pump on the base interval `[c+1, 2c]` by three explicit constructions. -/

/-- For a single false sum, `g = |(a+b) − c|` as a `Nat`. -/
theorem gnat_single (a b c : Nat) : gnat [⟨a,b,c⟩] = ((a : Int) + b - c).natAbs := by
  simp [gnat, FalseSum.delta, Nat.gcd_zero_right]

/-- When `a + b < c`, `g = c − a − b`. -/
theorem gnat_dneg (a b c : Nat) (h : a + b < c) : gnat [⟨a,b,c⟩] = c - a - b := by
  rw [gnat_single]; omega

/-- Gather `k` ones sitting at the front of a pile of `m` ones into one ball,
    leaving the other `m − k` ones: `1^m → k :: 1^(m−k)`.  Safe while
    `k ≤ max a b`. -/
theorem gatherPrefix (a b c : Nat) (k m : Nat)
    (hk1 : 1 ≤ k) (hk : k ≤ max a b) (hkm : k ≤ m) :
    Reach [⟨a,b,c⟩] (List.replicate m 1) (k :: List.replicate (m - k) 1) := by
  have hsplit : List.replicate m (1:Nat)
      = List.replicate k 1 ++ List.replicate (m - k) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have hg := reach_frame (List.replicate (m - k) 1) (gather a b c k hk1 hk)
  rw [hsplit]
  simpa using hg

/-- **Clean-range climb** (`c+1 ≤ n ≤ 2c−2`).  Scatter to ones, gather an `a`
    and a `b`, fire `{a,b} → c`, then reel the remaining ones onto the `c`. -/
theorem climbCleanLow (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c)
    (n : Nat) (hn1 : c + 1 ≤ n) (hn2 : n ≤ 2 * c - 2) :
    Reach [⟨a,b,c⟩] [n] [n + (c - a - b)] := by
  -- 1. scatter to ones
  have s1 : Reach [⟨a,b,c⟩] [n] (List.replicate n 1) := getUnits a b c n hn1 hn2
  -- 2. gather an `a` at the front
  have s2 : Reach [⟨a,b,c⟩] (List.replicate n 1) (a :: List.replicate (n - a) 1) :=
    gatherPrefix a b c a n ha (by omega) (by omega)
  -- 3. gather a `b` right after it
  have gb : Reach [⟨a,b,c⟩] (List.replicate (n - a) 1) (b :: List.replicate (n - a - b) 1) :=
    gatherPrefix a b c b (n - a) hb (by omega) (by omega)
  have s3 : Reach [⟨a,b,c⟩] (a :: List.replicate (n - a) 1)
      (a :: b :: List.replicate (n - a - b) 1) := by
    have := reach_frame_left [a] gb
    simpa using this
  -- 4. fire {a,b} → c
  have s4 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (n - a - b) 1)
      (c :: List.replicate (n - a - b) 1) := by
    have hm := reach_move (List.replicate (n - a - b) 1)
      (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  -- 5. reel the remaining ones onto the c (c > max a b)
  have s5 : Reach [⟨a,b,c⟩] (c :: List.replicate (n - a - b) 1) [c + (n - a - b)] :=
    mergeUnitsHi a b c (n - a - b) c (by omega)
  have e : c + (n - a - b) = n + (c - a - b) := by omega
  rw [e] at s5
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 (reach_trans s4 s5)))


/-- Perm helper: a `c` at the front and a `c` at the very back of a pile of ones
    can be brought together. -/
theorem perm_two_c (c k : Nat) :
    (c :: (List.replicate k 1 ++ [c])).Perm (c :: c :: List.replicate k 1) := by
  have h : (List.replicate k (1:Nat) ++ [c]).Perm (c :: List.replicate k 1) :=
    List.perm_append_comm
  exact h.cons c

/-- **Boundary climb at `n = 2c−1`.**  Split to `[c−1, c]`; scatter the `c−1`,
    gather an `a` and `b` from those ones, fire to make a *second* `c`, merge the
    two `c`s to `2c`, and reel the leftover `g−1` ones on. -/
theorem climb2cm1 (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c) :
    Reach [⟨a,b,c⟩] [2 * c - 1] [(2 * c - 1) + (c - a - b)] := by
  -- 1. n = 2c−1 splits to [c−1, c]
  have hsp : Reach [⟨a,b,c⟩] [2 * c - 1] [(2*c-1)/2, (2*c-1+1)/2] :=
    reach_move [] (Local.nsplit (2*c-1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c-1)/2 = c - 1 := by omega
  have hd2 : (2*c-1+1)/2 = c := by omega
  rw [hd1, hd2] at hsp
  -- 2. scatter the c−1 (it is < c), keeping the c on the right
  have sc : Reach [⟨a,b,c⟩] [c-1] (List.replicate (c-1) 1) :=
    scatterClean a b c (c-1) (by omega) (by omega)
  have s2 : Reach [⟨a,b,c⟩] [c-1, c] (List.replicate (c-1) 1 ++ [c]) := by
    have := reach_frame [c] sc; simpa using this
  -- 3. gather an a from the prefix of those c−1 ones
  have ga : Reach [⟨a,b,c⟩] (List.replicate (c-1) 1) (a :: List.replicate (c-1-a) 1) :=
    gatherPrefix a b c a (c-1) ha (by omega) (by omega)
  have s3 : Reach [⟨a,b,c⟩] (List.replicate (c-1) 1 ++ [c])
      (a :: (List.replicate (c-1-a) 1 ++ [c])) := by
    have := reach_frame [c] ga; simpa using this
  -- 4. gather a b right after the a
  have gb : Reach [⟨a,b,c⟩] (List.replicate (c-1-a) 1) (b :: List.replicate (c-1-a-b) 1) :=
    gatherPrefix a b c b (c-1-a) hb (by omega) (by omega)
  have s4 : Reach [⟨a,b,c⟩] (a :: (List.replicate (c-1-a) 1 ++ [c]))
      (a :: b :: (List.replicate (c-1-a-b) 1 ++ [c])) := by
    have := reach_frame_left [a] (reach_frame [c] gb); simpa using this
  -- 5. fire {a,b} → c  (now two c's, plus g−1 ones in between)
  have s5 : Reach [⟨a,b,c⟩] (a :: b :: (List.replicate (c-1-a-b) 1 ++ [c]))
      (c :: (List.replicate (c-1-a-b) 1 ++ [c])) := by
    have hm := reach_move (List.replicate (c-1-a-b) 1 ++ [c])
      (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  -- 6. merge the two c's into 2c
  have s6 : Reach [⟨a,b,c⟩] (c :: (List.replicate (c-1-a-b) 1 ++ [c]))
      (2 * c :: List.replicate (c-1-a-b) 1) := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = c ∧ f.b = c) ∨ (f.a = c ∧ f.b = c)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move (List.replicate (c-1-a-b) 1) (Local.nmerge c c hcc)
      (perm_two_c c (c-1-a-b)) (Reach.refl _)
    have e : c + c = 2 * c := by omega
    rw [e] at hm
    simpa using hm
  -- 7. reel the leftover g−1 ones onto the 2c
  have s7 : Reach [⟨a,b,c⟩] (2 * c :: List.replicate (c-1-a-b) 1) [2*c + (c-1-a-b)] :=
    mergeUnitsHi a b c (c-1-a-b) (2*c) (by omega)
  have e : 2*c + (c-1-a-b) = (2 * c - 1) + (c - a - b) := by omega
  rw [e] at s7
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 (reach_trans s4
    (reach_trans s5 (reach_trans s6 s7)))))


/-- Scatter every ball of a list, each `< c`, down to ones: `l → 1^(total l)`. -/
theorem scatterList (a b c : Nat) :
    ∀ l : List Nat, (∀ x ∈ l, 1 ≤ x ∧ x < c) →
      Reach [⟨a,b,c⟩] l (List.replicate (total l) 1) := by
  intro l
  induction l with
  | nil => intro _; exact Reach.refl _
  | cons x xs ih =>
    intro hx
    have hx0 := hx x (by simp)
    have sc : Reach [⟨a,b,c⟩] [x] (List.replicate x 1) :=
      scatterClean a b c x hx0.1 hx0.2
    have s1 : Reach [⟨a,b,c⟩] (x :: xs) (List.replicate x 1 ++ xs) := by
      have := reach_frame xs sc; simpa using this
    have s2 : Reach [⟨a,b,c⟩] xs (List.replicate (total xs) 1) :=
      ih (fun y hy => hx y (by simp [hy]))
    have s3 : Reach [⟨a,b,c⟩] (List.replicate x 1 ++ xs)
        (List.replicate x 1 ++ List.replicate (total xs) 1) := reach_frame_left _ s2
    have e : List.replicate x (1:Nat) ++ List.replicate (total xs) 1
        = List.replicate (total (x :: xs)) 1 := by
      rw [total_cons]; exact replicate_one_add x (total xs)
    rw [e] at s3
    exact reach_trans s1 s3

/-- Rotation perm `[a,b,c] ~ [b,c,a]`. -/
theorem perm_abc_bca (a b c : Nat) :
    ([a, b, c]).Perm ([b, c, a]) := by
  have h1 : ([a, b, c]).Perm ([b, a, c]) := List.Perm.swap b a [c]
  have h2 : ([b, a, c]).Perm ([b, c, a]) := (List.Perm.swap c a []).cons b
  exact h1.trans h2

/-- Rotation perm `c :: a :: b :: L ~ a :: b :: c :: L`. -/
theorem perm_c_ab (a b c : Nat) (L : List Nat) :
    (c :: a :: b :: L).Perm (a :: b :: c :: L) := by
  have h1 : (c :: a :: b :: L).Perm (a :: c :: b :: L) := List.Perm.swap a c (b :: L)
  have h2 : (a :: c :: b :: L).Perm (a :: b :: c :: L) := (List.Perm.swap b c L).cons a
  exact h1.trans h2

/-- **The `n = 2c` dip.**  `2c` splits only to `{c,c}` (both locked), so `{a,b}`
    cannot be formed at total `2c`.  Reach `2c + g` by: unlock one `c` (false
    split), merge its `b` with the other `c` to break the lock *without* losing
    `g`, split that, scatter everything to ones, regather *two* `{a,b}` pairs plus
    `g` carry-ones, fire both pairs, and merge the two fresh `c`s with the carry. -/
theorem climb2c (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c) :
    Reach [⟨a,b,c⟩] [2 * c] [2 * c + (c - a - b)] := by
  obtain ⟨g, hg⟩ : ∃ g, c - a - b = g := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, a + b + c = N := ⟨_, rfl⟩
  rw [hg]
  -- 1. 2c → [c, c]
  have hsp : Reach [⟨a,b,c⟩] [2 * c] [(2*c)/2, (2*c+1)/2] :=
    reach_move [] (Local.nsplit (2*c) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c)/2 = c := by omega
  have hd2 : (2*c+1)/2 = c := by omega
  rw [hd1, hd2] at hsp
  -- 2. fsplit one c → [a, b, c]
  have s2 : Reach [⟨a,b,c⟩] [c, c] [a, b, c] := by
    have hm := reach_move [c] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  -- 3. merge b with c (normal: {b,c} ≠ {a,b}), keeping a → [b+c, a]
  have s3 : Reach [⟨a,b,c⟩] [a, b, c] [b + c, a] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = b ∧ f.b = c) ∨ (f.a = c ∧ f.b = b)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [a] (Local.nmerge b c hcc) (perm_abc_bca a b c) (Reach.refl _)
    simpa using hm
  -- 4. split b+c → [h1, h2, a], both halves < c
  have s4 : Reach [⟨a,b,c⟩] [b + c, a] [(b+c)/2, (b+c+1)/2, a] := by
    have hm := reach_move [a] (Local.nsplit (cfg := [⟨a,b,c⟩]) (b+c) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  -- 5. scatter [h1, h2, a] to ones (total = a+b+c = N)
  have s5 : Reach [⟨a,b,c⟩] [(b+c)/2, (b+c+1)/2, a] (List.replicate N 1) := by
    have hb1 : 1 ≤ (b+c)/2 ∧ (b+c)/2 < c := by omega
    have hb2 : 1 ≤ (b+c+1)/2 ∧ (b+c+1)/2 < c := by omega
    have hba : 1 ≤ a ∧ a < c := ⟨ha, by omega⟩
    have hsc := scatterList a b c [(b+c)/2, (b+c+1)/2, a] (by
      intro x hx
      rcases List.mem_cons.1 hx with h | hx; · rw [h]; exact hb1
      rcases List.mem_cons.1 hx with h | hx; · rw [h]; exact hb2
      rw [List.mem_singleton] at hx; rw [hx]; exact hba)
    have e : total [(b+c)/2, (b+c+1)/2, a] = N := by simp only [total_cons, total_nil]; omega
    rw [e] at hsc; exact hsc
  -- 6. gather a, b, a, b off the front → [a,b,a,b] ++ 1^g
  have ga0 : Reach [⟨a,b,c⟩] (List.replicate N 1) (a :: List.replicate (N - a) 1) :=
    gatherPrefix a b c a N ha (by omega) (by omega)
  have gb1 : Reach [⟨a,b,c⟩] (List.replicate (N-a) 1) (b :: List.replicate (N-a-b) 1) :=
    gatherPrefix a b c b (N-a) hb (by omega) (by omega)
  have ga2 : Reach [⟨a,b,c⟩] (List.replicate (N-a-b) 1) (a :: List.replicate (N-a-b-a) 1) :=
    gatherPrefix a b c a (N-a-b) ha (by omega) (by omega)
  have gb3 : Reach [⟨a,b,c⟩] (List.replicate (N-a-b-a) 1) (b :: List.replicate (N-a-b-a-b) 1) :=
    gatherPrefix a b c b (N-a-b-a) hb (by omega) (by omega)
  have s6 : Reach [⟨a,b,c⟩] (List.replicate N 1)
      (a :: b :: a :: b :: List.replicate g 1) := by
    have e : N - a - b - a - b = g := by omega
    rw [e] at gb3
    have r1 := ga0
    have r2 := reach_frame_left [a] gb1
    have r3 := reach_frame_left [a, b] ga2
    have r4 := reach_frame_left [a, b, a] gb3
    have c1 : Reach [⟨a,b,c⟩] (List.replicate N 1) (a :: b :: List.replicate (N-a-b) 1) := by
      have := reach_trans r1 (by simpa using r2); simpa using this
    have c2 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (N-a-b) 1)
        (a :: b :: a :: List.replicate (N-a-b-a) 1) := by simpa using r3
    have c3 : Reach [⟨a,b,c⟩] (a :: b :: a :: List.replicate (N-a-b-a) 1)
        (a :: b :: a :: b :: List.replicate g 1) := by simpa using r4
    exact reach_trans c1 (reach_trans c2 c3)
  -- 7. fire the front pair {a,b} → c
  have s7 : Reach [⟨a,b,c⟩] (a :: b :: a :: b :: List.replicate g 1)
      (c :: a :: b :: List.replicate g 1) := by
    have hm := reach_move (a :: b :: List.replicate g 1)
      (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  -- 8. fire the remaining pair {a,b} → c (reorder c past it)
  have s8 : Reach [⟨a,b,c⟩] (c :: a :: b :: List.replicate g 1)
      (c :: c :: List.replicate g 1) := by
    have hm := reach_move (c :: List.replicate g 1)
      (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (perm_c_ab a b c (List.replicate g 1))
      (Reach.refl _)
    simpa using hm
  -- 9. merge the two c's into 2c
  have s9 : Reach [⟨a,b,c⟩] (c :: c :: List.replicate g 1) (2 * c :: List.replicate g 1) := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = c ∧ f.b = c) ∨ (f.a = c ∧ f.b = c)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move (List.replicate g 1) (Local.nmerge c c hcc)
      (List.Perm.refl _) (Reach.refl _)
    have e : c + c = 2 * c := by omega
    rw [e] at hm; simpa using hm
  -- 10. reel the g carry-ones onto 2c
  have s10 : Reach [⟨a,b,c⟩] (2 * c :: List.replicate g 1) [2 * c + g] :=
    mergeUnitsHi a b c g (2*c) (by omega)
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 (reach_trans s4 (reach_trans s5
    (reach_trans s6 (reach_trans s7 (reach_trans s8 (reach_trans s9 s10))))))))


/-- For `a + b < c`, `H = c`. -/
theorem Hnat_dneg (a b c : Nat) (hab : a + b < c) : Hnat [⟨a,b,c⟩] = c := by
  show max (max (a + b) c) 0 = c; omega

/-- **The climb base, fully discharged for `a + b < c`.**  Covers the whole base
    interval `[c+1, 2c]` by the three constructions above. -/
theorem baseC_dneg (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]] := by
  have hH : Hnat [⟨a,b,c⟩] = c := Hnat_dneg a b c hab
  have hMv : Mval [⟨a,b,c⟩] = c + 1 := by show Hnat [⟨a,b,c⟩] + 1 = c + 1; rw [hH]
  have hgn : gnat [⟨a,b,c⟩] = c - a - b := gnat_dneg a b c hab
  intro n hn1 hn2
  have hn1' : c + 1 ≤ n := by omega
  have hn2' : n ≤ 2 * c := by omega
  rw [hgn]
  by_cases hle : n ≤ 2 * c - 2
  · exact climbCleanLow a b c ha hb hab n hn1' hle
  · rcases Nat.lt_or_ge n (2 * c) with hlt | hge
    · have he : n = 2 * c - 1 := by omega
      rw [he]; exact climb2cm1 a b c ha hb hab
    · have he : n = 2 * c := by omega
      rw [he]; exact climb2c a b c ha hb hab

/-- **The full climb pump for `a + b < c`** (unconditional): every `n ≥ M`
    climbs by `g`.  Combines `baseC_dneg` with the symbolic halving recursion. -/
theorem climb_dneg (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]] :=
  climb_of_base a b c ha hb (by omega) (by omega) (baseC_dneg a b c ha hb hab)


/-! ### Toward the descend pump for `a + b < c`, when both legs are `≥ 2`

With `2 ≤ a, b` the value `1` is not one of the legs, so a "+1 accumulator" can
build *any* ball from ones without ever forming the forbidden pair `{a,b}`
(`gatherBig`).  That removes the only obstruction to harvesting a `c`, which is
what descend needs. -/

/-- Cap-free gather: when `2 ≤ a, b`, build *any* `k` from `k` ones (the `+1`
    accumulator step `{k,1}` is never `{a,b}` since `1 ∉ {a,b}`). -/
theorem gatherBig (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) :
    ∀ k, 1 ≤ k → Reach [⟨a,b,c⟩] (List.replicate k 1) [k] := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; exact Reach.refl _
    · have prev := ih hkpos
      have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config),
          ¬ ((f.a = 1 ∧ f.b = k) ∨ (f.a = k ∧ f.b = 1)) := by
        simp only [List.mem_singleton, forall_eq]; omega
      have step2 : Reach [⟨a,b,c⟩] [1, k] [k + 1] := by
        have hm := reach_move [] (Local.nmerge 1 k hcc) (List.Perm.refl _) (Reach.refl _)
        have e : 1 + k = k + 1 := by omega
        rwa [e] at hm
      exact reach_trans (reach_frame_left [1] prev) step2

/-- **Lose `g` from a pile of ones.**  Build a fresh `c` from `c` of the ones,
    false-split it to `{a,b}` (dropping the total by `g`), and scatter the legs
    back to ones: `1^m → 1^(m−g)`. -/
theorem loseG (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ m, c ≤ m → Reach [⟨a,b,c⟩] (List.replicate m 1) (List.replicate (m - (c - a - b)) 1) := by
  intro m hm
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherBig a b c ha2 hb2 c (by omega)
  have hsplitrep : List.replicate m (1:Nat) = List.replicate c 1 ++ List.replicate (m - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨a,b,c⟩] (List.replicate m 1) (c :: List.replicate (m - c) 1) := by
    rw [hsplitrep]; have := reach_frame (List.replicate (m - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (c :: List.replicate (m - c) 1) (a :: b :: List.replicate (m - c) 1) := by
    have hm2 := reach_move (List.replicate (m - c) 1)
      (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm2
  have sca : Reach [⟨a,b,c⟩] [a] (List.replicate a 1) := scatterClean a b c a (by omega) (by omega)
  have scb : Reach [⟨a,b,c⟩] [b] (List.replicate b 1) := scatterClean a b c b (by omega) (by omega)
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (m - c) 1)
      (List.replicate a 1 ++ (b :: List.replicate (m - c) 1)) := by
    have := reach_frame (b :: List.replicate (m - c) 1) sca; simpa using this
  have s4 : Reach [⟨a,b,c⟩] (List.replicate a 1 ++ (b :: List.replicate (m - c) 1))
      (List.replicate a 1 ++ (List.replicate b 1 ++ List.replicate (m - c) 1)) := by
    have := reach_frame_left (List.replicate a 1) (reach_frame (List.replicate (m - c) 1) scb)
    simpa using this
  have ecat : List.replicate a (1:Nat) ++ (List.replicate b 1 ++ List.replicate (m - c) 1)
      = List.replicate (m - (c - a - b)) 1 := by
    rw [replicate_one_add, replicate_one_add]; congr 1; omega
  rw [ecat] at s4
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))


/-- Scatter a single non-`c` ball `≤ 2c−2` to ones (`scatterClean` below `c`,
    `getUnits` above). -/
theorem scatter1 (a b c : Nat) : ∀ v, 1 ≤ v → v ≤ 2 * c - 2 → v ≠ c →
    Reach [⟨a,b,c⟩] [v] (List.replicate v 1) := by
  intro v h1 h2 h3
  by_cases hlt : v < c
  · exact scatterClean a b c v h1 hlt
  · exact getUnits a b c v (by omega) h2

/-- Scatter a whole list of non-`c` balls (each `≤ 2c−2`) to ones. -/
theorem scatterListGen (a b c : Nat) :
    ∀ l : List Nat, (∀ x ∈ l, 1 ≤ x ∧ x ≤ 2 * c - 2 ∧ x ≠ c) →
      Reach [⟨a,b,c⟩] l (List.replicate (total l) 1) := by
  intro l
  induction l with
  | nil => intro _; exact Reach.refl _
  | cons x xs ih =>
    intro hx
    have hx0 := hx x (by simp)
    have sc : Reach [⟨a,b,c⟩] [x] (List.replicate x 1) :=
      scatter1 a b c x hx0.1 hx0.2.1 hx0.2.2
    have s1 : Reach [⟨a,b,c⟩] (x :: xs) (List.replicate x 1 ++ xs) := by
      have := reach_frame xs sc; simpa using this
    have s2 : Reach [⟨a,b,c⟩] xs (List.replicate (total xs) 1) :=
      ih (fun y hy => hx y (by simp [hy]))
    have s3 : Reach [⟨a,b,c⟩] (List.replicate x 1 ++ xs)
        (List.replicate x 1 ++ List.replicate (total xs) 1) := reach_frame_left _ s2
    have e : List.replicate x (1:Nat) ++ List.replicate (total xs) 1
        = List.replicate (total (x :: xs)) 1 := by
      rw [total_cons]; exact replicate_one_add x (total xs)
    rw [e] at s3
    exact reach_trans s1 s3

/-- Scatter a single ball in the high range `[2c+2, 2c+2g]` to ones: one split
    lands both halves in `[c+1, 2c−2]`, each scattered by `getUnits`. -/
theorem scatterHi (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hab : a + b < c) : ∀ m, 2 * c + 2 ≤ m →
    m ≤ 2 * c + 2 * (c - a - b) → Reach [⟨a,b,c⟩] [m] (List.replicate m 1) := by
  intro m h1 h2
  have hsplit : Reach [⟨a,b,c⟩] [m] [m / 2, (m + 1) / 2] :=
    reach_move [] (Local.nsplit m (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hsc1 := getUnits a b c (m / 2) (by omega) (by omega)
  have hsc2 := getUnits a b c ((m + 1) / 2) (by omega) (by omega)
  have step1 := reach_frame [(m + 1) / 2] hsc1
  have step2 := reach_frame_left (List.replicate (m / 2) 1) hsc2
  have hcat : List.replicate (m / 2) 1 ++ List.replicate ((m + 1) / 2) 1 = List.replicate m 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [hcat] at step2
  exact reach_trans hsplit (reach_trans step1 step2)


/-- Drop `2c−1` by `g` to ones.  Split to `[c−1, c]`; the `c` is a free harvest —
    false-split it and scatter the rest. -/
theorem descDrop_2cm1 (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c) :
    Reach [⟨a,b,c⟩] [2 * c - 1] (List.replicate (2 * c - 1 - (c - a - b)) 1) := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c - 1] [(2*c-1)/2, (2*c-1+1)/2] :=
    reach_move [] (Local.nsplit (2*c-1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c-1)/2 = c - 1 := by omega
  have hd2 : (2*c-1+1)/2 = c := by omega
  rw [hd1, hd2] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c - 1, c] [a, b, c - 1] := by
    have hm := reach_move [c - 1] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.swap c (c - 1) []) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c - 1] (List.replicate (total [a, b, c - 1]) 1) :=
    scatterListGen a b c [a, b, c - 1] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega, by omega⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega, by omega⟩
      rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega, by omega⟩)
  have e : total [a, b, c - 1] = 2 * c - 1 - (c - a - b) := by
    simp only [total_cons, total_nil]; omega
  rw [e] at s3
  exact reach_trans hsp (reach_trans s2 s3)

/-- Drop `2c` by `g` to ones.  `2c → [c,c]`; false-split one `c`, fold the
    leftover `c` into `a+c` (a normal ball `< 2c`), and scatter. -/
theorem descDrop_2c (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c) :
    Reach [⟨a,b,c⟩] [2 * c] (List.replicate (2 * c - (c - a - b)) 1) := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c] [(2*c)/2, (2*c+1)/2] :=
    reach_move [] (Local.nsplit (2*c) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c)/2 = c := by omega
  have hd2 : (2*c+1)/2 = c := by omega
  rw [hd1, hd2] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c, c] [a, b, c] := by
    have hm := reach_move [c] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c] [a + c, b] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = a ∧ f.b = c) ∨ (f.a = c ∧ f.b = a)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [b] (Local.nmerge a c hcc) ((List.Perm.swap c b []).cons a) (Reach.refl _)
    simpa using hm
  have s4 : Reach [⟨a,b,c⟩] [a + c, b] (List.replicate (total [a + c, b]) 1) :=
    scatterListGen a b c [a + c, b] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega, by omega⟩
      rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega, by omega⟩)
  have e : total [a + c, b] = 2 * c - (c - a - b) := by simp only [total_cons, total_nil]; omega
  rw [e] at s4
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 s4))

/-- Drop `2c+1` by `g` to ones.  `2c+1 → [c, c+1]`; false-split the `c`, scatter
    the rest (`c+1` is in range for `getUnits`). -/
theorem descDrop_2cp1 (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b < c) :
    Reach [⟨a,b,c⟩] [2 * c + 1] (List.replicate (2 * c + 1 - (c - a - b)) 1) := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c + 1] [(2*c+1)/2, (2*c+1+1)/2] :=
    reach_move [] (Local.nsplit (2*c+1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c+1)/2 = c := by omega
  have hd2 : (2*c+1+1)/2 = c + 1 := by omega
  rw [hd1, hd2] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c, c + 1] [a, b, c + 1] := by
    have hm := reach_move [c + 1] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c + 1] (List.replicate (total [a, b, c + 1]) 1) :=
    scatterListGen a b c [a, b, c + 1] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega, by omega⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega, by omega⟩
      rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega, by omega⟩)
  have e : total [a, b, c + 1] = 2 * c + 1 - (c - a - b) := by
    simp only [total_cons, total_nil]; omega
  rw [e] at s3
  exact reach_trans hsp (reach_trans s2 s3)

/-- **Drop a single ball by `g` to ones**, over the whole descend base range
    `[c+1+g, 2c+2g]` (legs `≥ 2`).  Scatterable values use `getUnits`/`scatterHi`
    then `loseG`; the three `c`-producing values `2c−1, 2c, 2c+1` are the boundary
    cases above. -/
theorem descDrop (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ m, c + 1 + (c - a - b) ≤ m → m ≤ 2 * c + 2 * (c - a - b) →
      Reach [⟨a,b,c⟩] [m] (List.replicate (m - (c - a - b)) 1) := by
  intro m h1 h2
  by_cases hA : m ≤ 2 * c - 2
  · exact reach_trans (getUnits a b c m (by omega) hA) (loseG a b c ha2 hb2 hab m (by omega))
  · by_cases hB : 2 * c + 2 ≤ m
    · exact reach_trans (scatterHi a b c ha2 hb2 hab m hB h2) (loseG a b c ha2 hb2 hab m (by omega))
    · have hcase : m = 2 * c - 1 ∨ m = 2 * c ∨ m = 2 * c + 1 := by omega
      rcases hcase with h | h | h
      · rw [h]; exact descDrop_2cm1 a b c (by omega) (by omega) hab
      · rw [h]; exact descDrop_2c a b c (by omega) (by omega) hab
      · rw [h]; exact descDrop_2cp1 a b c (by omega) (by omega) hab

/-- **The descend base, discharged for `a + b < c` with legs `≥ 2`.**  For each
    `n` in `[c+1, 2c+g]`, drop `[n+g]` to `n` ones (`descDrop`) then re-gather
    (`gatherBig`). -/
theorem baseD_dneg (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n] := by
  have hH : Hnat [⟨a,b,c⟩] = c := Hnat_dneg a b c hab
  have hMv : Mval [⟨a,b,c⟩] = c + 1 := by show Hnat [⟨a,b,c⟩] + 1 = c + 1; rw [hH]
  have hgn : gnat [⟨a,b,c⟩] = c - a - b := gnat_dneg a b c hab
  intro n hn1 hn2
  have hn1' : c + 1 ≤ n := by omega
  have hn2' : n ≤ 2 * c + (c - a - b) := by omega
  rw [hgn]
  have dd := descDrop a b c ha2 hb2 hab (n + (c - a - b)) (by omega) (by omega)
  have em : n + (c - a - b) - (c - a - b) = n := by omega
  rw [em] at dd
  have gg := gatherBig a b c ha2 hb2 n (by omega)
  exact reach_trans dd gg

/-- **Full unconditional sufficiency for `a + b < c` with legs `≥ 2`.**  This
    includes Classic `9+10=21`.  Both base pumps are now discharged symbolically
    (`baseC_dneg` climb, `baseD_dneg` descend), so `single_sufficiency_of_base`
    closes the characterization: every `s,t ≥ M` with `g ∣ (t−s)` is solvable. -/
theorem single_sufficiency_dneg (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  single_sufficiency_of_base a b c (by omega) (by omega) (by omega) (by omega)
    (baseC_dneg a b c (by omega) (by omega) hab)
    (baseD_dneg a b c ha2 hb2 hab)

/-- **Classic sufficiency, re-derived symbolically** from `single_sufficiency_dneg`
    (no BFS base cases): with `9 + 10 = 21` (`a,b ≥ 2`, `a+b < c`), every
    `s,t ≥ 22` with `2 ∣ (t−s)` is solvable. -/
theorem classic_sufficiency_symbolic {s t : Nat} (hs : 22 ≤ s) (ht : 22 ≤ t)
    (h : (2:Int) ∣ ((t:Int) - s)) : Reach classic [s] [t] :=
  single_sufficiency_dneg 9 10 21 (by decide) (by decide) (by decide) s t hs ht h


/-! ### The dual case `a + b > c` (`d > 0`), with legs in `[2, c)`

Now `c` is *below* `a + b`, so `H = a + b`, `g = a + b − c`, and the pumps swap
roles: **climb** harvests a `c` and false-splits it (`+g`), **descend** forms the
pair `{a,b}` and false-merges it (`−g`).  When `(a+b)/2 < c`, the single stuck
value `2c` sits in the base interval `[a+b+1, 2(a+b)]` and the scatter-problematic
values are again exactly `{2c−1, 2c, 2c+1}` — the same shape as the `a+b<c` case.
With `2 ≤ a, b`, reeling ones onto any base never forms `{a,b}` (`mergeUnitsLow`). -/

/-- When `c < a + b`, `H = a + b`. -/
theorem Hnat_dpos (a b c : Nat) (hab : c < a + b) : Hnat [⟨a,b,c⟩] = a + b := by
  show max (max (a + b) c) 0 = a + b; omega

/-- When `c < a + b`, `g = a + b − c`. -/
theorem gnat_dpos (a b c : Nat) (hab : c < a + b) : gnat [⟨a,b,c⟩] = a + b - c := by
  rw [gnat_single]; omega

/-- Reel `k` ones onto any base `v` when `2 ≤ a, b` (then `{v+i, 1} ≠ {a,b}` since
    `1 ∉ {a,b}`), regardless of how `v` compares to the legs. -/
theorem mergeUnitsLow (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) :
    ∀ k v, Reach [⟨a,b,c⟩] (v :: List.replicate k 1) [v + k] := by
  intro k
  induction k with
  | zero => intro v; exact Reach.refl _
  | succ k ih =>
    intro v
    have hc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = v ∧ f.b = 1) ∨ (f.a = 1 ∧ f.b = v)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move (List.replicate k 1) (Local.nmerge v 1 hc) (List.Perm.refl _) (Reach.refl _)
    have hrec := ih (v + 1)
    have e : (v + 1) + k = v + (k + 1) := by omega
    rw [e] at hrec
    exact reach_trans hm hrec


/-- Scatter a single ball in `[2c+2, 2(a+b)]` to ones: one split lands both
    halves in `[c+1, 2c−2]` (using `a+b ≤ 2c−2`), each scattered by `getUnits`. -/
theorem scatterHiPos (a b c : Nat) (hab : c < a + b) (hc2 : a + b ≤ 2 * c - 2) :
    ∀ m, 2 * c + 2 ≤ m → m ≤ 2 * (a + b) → Reach [⟨a,b,c⟩] [m] (List.replicate m 1) := by
  intro m h1 h2
  have hsplit : Reach [⟨a,b,c⟩] [m] [m / 2, (m + 1) / 2] :=
    reach_move [] (Local.nsplit m (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hsc1 := getUnits a b c (m / 2) (by omega) (by omega)
  have hsc2 := getUnits a b c ((m + 1) / 2) (by omega) (by omega)
  have step1 := reach_frame [(m + 1) / 2] hsc1
  have step2 := reach_frame_left (List.replicate (m / 2) 1) hsc2
  have hcat : List.replicate (m / 2) 1 ++ List.replicate ((m + 1) / 2) 1 = List.replicate m 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [hcat] at step2
  exact reach_trans hsplit (reach_trans step1 step2)

/-- Scatter any non-cluster base value `m ∈ [c+1, 2(a+b)] \ {2c−1, 2c, 2c+1}` to
    ones (`getUnits` below `2c−2`, `scatterHiPos` above `2c+2`). -/
theorem scatterPos (a b c : Nat) (hab : c < a + b) (hc2 : a + b ≤ 2 * c - 2) :
    ∀ m, c + 1 ≤ m → m ≤ 2 * (a + b) → m ≠ 2 * c - 1 → m ≠ 2 * c → m ≠ 2 * c + 1 →
      Reach [⟨a,b,c⟩] [m] (List.replicate m 1) := by
  intro m h1 h2 hne1 hne2 hne3
  by_cases hlo : m ≤ 2 * c - 2
  · exact getUnits a b c m h1 hlo
  · exact scatterHiPos a b c hab hc2 m (by omega) h2


/-- **Descend clean-range** (`d>0`): given `[m]` scattered to ones, gather an `a`
    and `b`, false-*merge* `{a,b} → c` (dropping `g`), and reel the rest onto the
    `c`.  Lands on `[c + (m−a−b)]`. -/
theorem descendCleanLow_pos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (m : Nat) (hsc : Reach [⟨a,b,c⟩] [m] (List.replicate m 1)) (hm : a + b ≤ m) :
    Reach [⟨a,b,c⟩] [m] [c + (m - a - b)] := by
  have s2 : Reach [⟨a,b,c⟩] (List.replicate m 1) (a :: List.replicate (m - a) 1) :=
    gatherPrefix a b c a m (by omega) (by omega) (by omega)
  have gb : Reach [⟨a,b,c⟩] (List.replicate (m - a) 1) (b :: List.replicate (m - a - b) 1) :=
    gatherPrefix a b c b (m - a) (by omega) (by omega) (by omega)
  have s3 : Reach [⟨a,b,c⟩] (a :: List.replicate (m - a) 1)
      (a :: b :: List.replicate (m - a - b) 1) := by
    have := reach_frame_left [a] gb; simpa using this
  have s4 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (m - a - b) 1)
      (c :: List.replicate (m - a - b) 1) := by
    have hm2 := reach_move (List.replicate (m - a - b) 1)
      (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm2
  have s5 : Reach [⟨a,b,c⟩] (c :: List.replicate (m - a - b) 1) [c + (m - a - b)] :=
    mergeUnitsLow a b c ha2 hb2 (m - a - b) c
  exact reach_trans hsc (reach_trans s2 (reach_trans s3 (reach_trans s4 s5)))

/-- **Climb clean-range** (`d>0`): given `[n]` scattered to ones, build a fresh
    `c` (`gatherBig`), false-*split* it to `{a,b}` (gaining `g`), and merge
    everything up.  Lands on `[n + (a+b−c)]`. -/
theorem climbCleanLow_pos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc : 1 ≤ c) (hab : c < a + b)
    (n : Nat) (hsc : Reach [⟨a,b,c⟩] [n] (List.replicate n 1)) (hn : c < n) :
    Reach [⟨a,b,c⟩] [n] [n + (a + b - c)] := by
  have hsplitrep : List.replicate n (1:Nat) = List.replicate c 1 ++ List.replicate (n - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherBig a b c ha2 hb2 c (by omega)
  have s1 : Reach [⟨a,b,c⟩] [n] (c :: List.replicate (n - c) 1) := by
    refine reach_trans hsc ?_
    rw [hsplitrep]; have := reach_frame (List.replicate (n - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (c :: List.replicate (n - c) 1) (a :: b :: List.replicate (n - c) 1) := by
    have hm2 := reach_move (List.replicate (n - c) 1)
      (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm2
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (n - c) 1) [a, b + (n - c)] := by
    have := reach_frame_left [a] (mergeUnitsLow a b c ha2 hb2 (n - c) b); simpa using this
  have s4 : Reach [⟨a,b,c⟩] [a, b + (n - c)] [n + (a + b - c)] := by
    have hnc : n - c ≠ 0 := by omega
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = a ∧ f.b = b + (n-c)) ∨ (f.a = b + (n-c) ∧ f.b = a)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [] (Local.nmerge a (b + (n - c)) hcc) (List.Perm.refl _) (Reach.refl _)
    have e : a + (b + (n - c)) = n + (a + b - c) := by omega
    rw [e] at hm; simpa using hm
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))


/-- Climb the cluster value `2c−1` (`d>0`, legs `< c`).  Split to `[c−1, c]`,
    false-split the `c` (gaining `g`), scatter everything (`< c`) to ones, and
    `gatherBig` up to the target. -/
theorem climb_2cm1_pos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) : Reach [⟨a,b,c⟩] [2 * c - 1] [(2 * c - 1) + (a + b - c)] := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c - 1] [(2*c-1)/2, (2*c-1+1)/2] :=
    reach_move [] (Local.nsplit (2*c-1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c-1)/2 = c - 1 := by omega
  have hd2 : (2*c-1+1)/2 = c := by omega
  rw [hd1, hd2] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c - 1, c] [a, b, c - 1] := by
    have hm := reach_move [c - 1] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.swap c (c - 1) []) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c - 1] (List.replicate (total [a, b, c - 1]) 1) :=
    scatterList a b c [a, b, c - 1] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega⟩
      rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩)
  have etot : total [a, b, c - 1] = (2 * c - 1) + (a + b - c) := by
    simp only [total_cons, total_nil]; omega
  rw [etot] at s3
  have s4 : Reach [⟨a,b,c⟩] (List.replicate ((2 * c - 1) + (a + b - c)) 1)
      [(2 * c - 1) + (a + b - c)] := gatherBig a b c ha2 hb2 _ (by omega)
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 s4))

/-- Climb the stuck value `2c` (`d>0`).  `2c → [c,c]`; false-split one `c`
    (gaining `g`), fold the leftover `c` into `a+c`, merge up. -/
theorem climb_2c_pos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) : Reach [⟨a,b,c⟩] [2 * c] [2 * c + (a + b - c)] := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c] [(2*c)/2, (2*c+1)/2] :=
    reach_move [] (Local.nsplit (2*c) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c)/2 = c := by omega
  have hd2 : (2*c+1)/2 = c := by omega
  rw [hd1, hd2] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c, c] [a, b, c] := by
    have hm := reach_move [c] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c] [a + c, b] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = a ∧ f.b = c) ∨ (f.a = c ∧ f.b = a)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [b] (Local.nmerge a c hcc) ((List.Perm.swap c b []).cons a) (Reach.refl _)
    simpa using hm
  have s4 : Reach [⟨a,b,c⟩] [a + c, b] [2 * c + (a + b - c)] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = a + c ∧ f.b = b) ∨ (f.a = b ∧ f.b = a + c)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [] (Local.nmerge (a + c) b hcc) (List.Perm.refl _) (Reach.refl _)
    have e : (a + c) + b = 2 * c + (a + b - c) := by omega
    rw [e] at hm; simpa using hm
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 s4))

/-- Climb the cluster value `2c+1` (`d>0`).  `2c+1 → [c, c+1]`; false-split the
    `c`, fold the (normal) `c+1` into `a+c+1`, merge up. -/
theorem climb_2cp1_pos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) : Reach [⟨a,b,c⟩] [2 * c + 1] [(2 * c + 1) + (a + b - c)] := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c + 1] [(2*c+1)/2, (2*c+1+1)/2] :=
    reach_move [] (Local.nsplit (2*c+1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hd1 : (2*c+1)/2 = c := by omega
  have hd2 : (2*c+1+1)/2 = c + 1 := by omega
  rw [hd1, hd2] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c, c + 1] [a, b, c + 1] := by
    have hm := reach_move [c + 1] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c + 1] [a + (c + 1), b] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = a ∧ f.b = c + 1) ∨ (f.a = c + 1 ∧ f.b = a)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [b] (Local.nmerge a (c + 1) hcc) ((List.Perm.swap (c+1) b []).cons a)
      (Reach.refl _)
    simpa using hm
  have s4 : Reach [⟨a,b,c⟩] [a + (c + 1), b] [(2 * c + 1) + (a + b - c)] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = a + (c+1) ∧ f.b = b) ∨ (f.a = b ∧ f.b = a + (c+1))) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [] (Local.nmerge (a + (c + 1)) b hcc) (List.Perm.refl _) (Reach.refl _)
    have e : (a + (c + 1)) + b = (2 * c + 1) + (a + b - c) := by omega
    rw [e] at hm; simpa using hm
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 s4))


/-- **The climb base, discharged for `a+b > c` with legs in `[2, c)`.**  Covers
    `[a+b+1, 2(a+b)]`: clean values scatter then build/fsplit/merge
    (`climbCleanLow_pos`); the cluster `2c−1, 2c, 2c+1` use the boundary lemmas. -/
theorem baseC_dpos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]] := by
  have hH : Hnat [⟨a,b,c⟩] = a + b := Hnat_dpos a b c hab
  have hMv : Mval [⟨a,b,c⟩] = a + b + 1 := by show Hnat [⟨a,b,c⟩] + 1 = a + b + 1; rw [hH]
  have hgn : gnat [⟨a,b,c⟩] = a + b - c := gnat_dpos a b c hab
  have hc2 : a + b ≤ 2 * c - 2 := by omega
  intro n hn1 hn2
  have hn1' : a + b + 1 ≤ n := by omega
  have hn2' : n ≤ 2 * (a + b) := by omega
  rw [hgn]
  by_cases he1 : n = 2 * c - 1
  · rw [he1]; exact climb_2cm1_pos a b c ha2 hb2 hac hbc hab
  · by_cases he2 : n = 2 * c
    · rw [he2]; exact climb_2c_pos a b c ha2 hb2 hac hbc hab
    · by_cases he3 : n = 2 * c + 1
      · rw [he3]; exact climb_2cp1_pos a b c ha2 hb2 hac hbc hab
      · have hsc := scatterPos a b c hab hc2 n (by omega) (by omega) he1 he2 he3
        exact climbCleanLow_pos a b c ha2 hb2 (by omega) hab n hsc (by omega)

/-- **The full climb pump for `a+b > c`** (legs in `[2, c)`): every `n ≥ M`
    climbs by `g`, via the halving recursion `climb_of_base` and `baseC_dpos`. -/
theorem climb_dpos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]] :=
  climb_of_base a b c (by omega) (by omega) (by omega) (by omega)
    (baseC_dpos a b c ha2 hb2 hac hbc hab)


/-! ### The descend pump for `a+b > c` (single-cluster sub-family)

For `2 ≤ a, b`, `a < c`, `b < c`, `c < a + b`, and `2(a+b)+2 ≤ 3c` (so the only
stuck value in the descend base is `2c`, with clean halving everywhere else —
e.g. `3+3=5`, `3+4=6`, `5+5=8`), the descend pump mirrors the `a+b<c` `descDrop`:
scatter `[m]` to `m` ones, then drop `g` with `loseGpos`. The new ingredient is
**unlocking** a locked `c`: merge a unit onto it (`c → c+1`, normal) and `getUnits`. -/

/-- Unlock and scatter a locked `c` given `K ≥ 1` spare ones:
    `c :: 1^K → 1^(c+K)`. -/
theorem unlockC (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 3 ≤ c) :
    ∀ K, 1 ≤ K → Reach [⟨a,b,c⟩] (c :: List.replicate K 1) (List.replicate (c + K) 1) := by
  intro K hK
  have hrK : List.replicate K (1:Nat) = 1 :: List.replicate (K - 1) 1 := by
    cases K with
    | zero => omega
    | succ n => simp [List.replicate_succ]
  have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = c ∧ f.b = 1) ∨ (f.a = 1 ∧ f.b = c)) := by
    simp only [List.mem_singleton, forall_eq]; omega
  have s1 : Reach [⟨a,b,c⟩] (c :: List.replicate K 1) ((c + 1) :: List.replicate (K - 1) 1) := by
    rw [hrK]
    have hm := reach_move (List.replicate (K - 1) 1) (Local.nmerge c 1 hcc)
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have gu : Reach [⟨a,b,c⟩] [c + 1] (List.replicate (c + 1) 1) :=
    getUnits a b c (c + 1) (by omega) (by omega)
  have s2 : Reach [⟨a,b,c⟩] ((c + 1) :: List.replicate (K - 1) 1)
      (List.replicate (c + 1) 1 ++ List.replicate (K - 1) 1) := by
    have := reach_frame (List.replicate (K - 1) 1) gu; simpa using this
  have ecat : List.replicate (c + 1) (1:Nat) ++ List.replicate (K - 1) 1 = List.replicate (c + K) 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [ecat] at s2
  exact reach_trans s1 s2

/-- **Drop `g` from a pile of ones** (`d>0`): gather `{a,b}`, false-merge to `c`,
    then unlock that `c`.  `1^K → 1^(K−g)` for `K ≥ a+b+1`. -/
theorem loseGpos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) :
    ∀ K, a + b + 1 ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - (a + b - c)) 1) := by
  intro K hK
  have ga : Reach [⟨a,b,c⟩] (List.replicate K 1) (a :: List.replicate (K - a) 1) :=
    gatherPrefix a b c a K (by omega) (by omega) (by omega)
  have gb : Reach [⟨a,b,c⟩] (List.replicate (K - a) 1) (b :: List.replicate (K - a - b) 1) :=
    gatherPrefix a b c b (K - a) (by omega) (by omega) (by omega)
  have s2 : Reach [⟨a,b,c⟩] (a :: List.replicate (K - a) 1) (a :: b :: List.replicate (K - a - b) 1) := by
    have := reach_frame_left [a] gb; simpa using this
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (K - a - b) 1) (c :: List.replicate (K - a - b) 1) := by
    have hm := reach_move (List.replicate (K - a - b) 1)
      (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s4 : Reach [⟨a,b,c⟩] (c :: List.replicate (K - a - b) 1) (List.replicate (c + (K - a - b)) 1) :=
    unlockC a b c ha2 hb2 (by omega) (K - a - b) (by omega)
  have e : c + (K - a - b) = K - (a + b - c) := by omega
  rw [e] at s4
  exact reach_trans ga (reach_trans s2 (reach_trans s3 s4))


/-- Drop `2c−1` to ones (`d>0`).  Split to `[c−1,c]`, false-split the `c`, scatter
    everything `< c`, then `loseGpos` twice. -/
theorem descToOnes_2cm1 (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) : Reach [⟨a,b,c⟩] [2 * c - 1] (List.replicate (2 * c - 1 - (a + b - c)) 1) := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c - 1] [(2*c-1)/2, (2*c-1+1)/2] :=
    reach_move [] (Local.nsplit (2*c-1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  rw [show (2*c-1)/2 = c - 1 from by omega, show (2*c-1+1)/2 = c from by omega] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c - 1, c] [a, b, c - 1] := by
    have hm := reach_move [c - 1] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.swap c (c - 1) []) (Reach.refl _); simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c - 1] (List.replicate (a + b + c - 1) 1) := by
    have h := scatterList a b c [a, b, c - 1] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx; · exact ⟨by omega, by omega⟩
      rcases List.mem_cons.1 hx with rfl | hx; · exact ⟨by omega, by omega⟩
      rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩)
    rwa [show total [a, b, c - 1] = a + b + c - 1 from by simp only [total_cons, total_nil]; omega] at h
  have l1 := loseGpos a b c ha2 hb2 hac hbc hab (a + b + c - 1) (by omega)
  rw [show a + b + c - 1 - (a + b - c) = 2 * c - 1 from by omega] at l1
  have l2 := loseGpos a b c ha2 hb2 hac hbc hab (2 * c - 1) (by omega)
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 (reach_trans l1 l2)))

/-- Drop `2c` to ones (`d>0`).  `2c → [c,c]`, false-split *both* `c`s to
    `[a,b,a,b]`, scatter, then `loseGpos` three times. -/
theorem descToOnes_2c (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) : Reach [⟨a,b,c⟩] [2 * c] (List.replicate (2 * c - (a + b - c)) 1) := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c] [(2*c)/2, (2*c+1)/2] :=
    reach_move [] (Local.nsplit (2*c) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  rw [show (2*c)/2 = c from by omega, show (2*c+1)/2 = c from by omega] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c, c] [a, b, c] := by
    have hm := reach_move [c] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _); simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c] [a, b, a, b] := by
    have hm := reach_move [a, b] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (perm_c_ab a b c []).symm (Reach.refl _); simpa using hm
  have s4 : Reach [⟨a,b,c⟩] [a, b, a, b] (List.replicate (2 * (a + b)) 1) := by
    have h := scatterList a b c [a, b, a, b] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx; · exact ⟨by omega, by omega⟩
      rcases List.mem_cons.1 hx with rfl | hx; · exact ⟨by omega, by omega⟩
      rcases List.mem_cons.1 hx with rfl | hx; · exact ⟨by omega, by omega⟩
      rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩)
    rwa [show total [a, b, a, b] = 2 * (a + b) from by simp only [total_cons, total_nil]; omega] at h
  have l1 := loseGpos a b c ha2 hb2 hac hbc hab (2 * (a + b)) (by omega)
  rw [show 2 * (a + b) - (a + b - c) = a + b + c from by omega] at l1
  have l2 := loseGpos a b c ha2 hb2 hac hbc hab (a + b + c) (by omega)
  rw [show a + b + c - (a + b - c) = 2 * c from by omega] at l2
  have l3 := loseGpos a b c ha2 hb2 hac hbc hab (2 * c) (by omega)
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 (reach_trans s4
    (reach_trans l1 (reach_trans l2 l3)))))

/-- Drop `2c+1` to ones (`d>0`).  `2c+1 → [c, c+1]`, false-split the `c`, scatter
    (the normal `c+1` via `getUnits`), then `loseGpos` twice. -/
theorem descToOnes_2cp1 (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) : Reach [⟨a,b,c⟩] [2 * c + 1] (List.replicate (2 * c + 1 - (a + b - c)) 1) := by
  have hsp : Reach [⟨a,b,c⟩] [2 * c + 1] [(2*c+1)/2, (2*c+1+1)/2] :=
    reach_move [] (Local.nsplit (2*c+1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  rw [show (2*c+1)/2 = c from by omega, show (2*c+1+1)/2 = c + 1 from by omega] at hsp
  have s2 : Reach [⟨a,b,c⟩] [c, c + 1] [a, b, c + 1] := by
    have hm := reach_move [c + 1] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _); simpa using hm
  have s3 : Reach [⟨a,b,c⟩] [a, b, c + 1] (List.replicate (a + b + c + 1) 1) := by
    have h := scatterListGen a b c [a, b, c + 1] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx; · exact ⟨by omega, by omega, by omega⟩
      rcases List.mem_cons.1 hx with rfl | hx; · exact ⟨by omega, by omega, by omega⟩
      rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega, by omega⟩)
    rwa [show total [a, b, c + 1] = a + b + c + 1 from by simp only [total_cons, total_nil]; omega] at h
  have l1 := loseGpos a b c ha2 hb2 hac hbc hab (a + b + c + 1) (by omega)
  rw [show a + b + c + 1 - (a + b - c) = 2 * c + 1 from by omega] at l1
  have l2 := loseGpos a b c ha2 hb2 hac hbc hab (2 * c + 1) (by omega)
  exact reach_trans hsp (reach_trans s2 (reach_trans s3 (reach_trans l1 l2)))


/-- **Drop `[m]` to `m−g` ones** across the descend base range, for the
    single-cluster family (`2(a+b)+2 ≤ 3c`).  Clean values scatter then `loseGpos`;
    the cluster `2c−1, 2c, 2c+1` use the boundary lemmas. -/
theorem descToOnes_pos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) (hc3 : 2 * (a + b) + 2 ≤ 3 * c) :
    ∀ m, a + b + 1 ≤ m → m ≤ 2 * (a + b) + 2 * (a + b - c) →
      Reach [⟨a,b,c⟩] [m] (List.replicate (m - (a + b - c)) 1) := by
  intro m hm1 hm2
  by_cases he1 : m = 2 * c - 1
  · rw [he1]; exact descToOnes_2cm1 a b c ha2 hb2 hac hbc hab
  · by_cases he2 : m = 2 * c
    · rw [he2]; exact descToOnes_2c a b c ha2 hb2 hac hbc hab
    · by_cases he3 : m = 2 * c + 1
      · rw [he3]; exact descToOnes_2cp1 a b c ha2 hb2 hac hbc hab
      · by_cases hlo : m ≤ 2 * c - 2
        · exact reach_trans (getUnits a b c m (by omega) hlo)
            (loseGpos a b c ha2 hb2 hac hbc hab m (by omega))
        · -- m ≥ 2c+2: one split, getUnits both halves, then loseGpos
          have hsplit : Reach [⟨a,b,c⟩] [m] [m / 2, (m + 1) / 2] :=
            reach_move [] (Local.nsplit m (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          have gu1 := getUnits a b c (m / 2) (by omega) (by omega)
          have gu2 := getUnits a b c ((m + 1) / 2) (by omega) (by omega)
          have step1 := reach_frame [(m + 1) / 2] gu1
          have step2 := reach_frame_left (List.replicate (m / 2) 1) gu2
          have hcat : List.replicate (m / 2) 1 ++ List.replicate ((m + 1) / 2) 1 = List.replicate m 1 := by
            rw [replicate_one_add]; congr 1; omega
          rw [hcat] at step2
          have scat : Reach [⟨a,b,c⟩] [m] (List.replicate m 1) :=
            reach_trans hsplit (reach_trans step1 step2)
          exact reach_trans scat (loseGpos a b c ha2 hb2 hac hbc hab m (by omega))

/-- **The descend base, discharged for `a+b > c`** (single-cluster family).  For
    each `n` in `[M, 2H+g]`, drop `[n+g]` to `n` ones (`descToOnes_pos`) then
    re-gather (`gatherBig`). -/
theorem baseD_dpos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) (hc3 : 2 * (a + b) + 2 ≤ 3 * c) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n] := by
  have hH : Hnat [⟨a,b,c⟩] = a + b := Hnat_dpos a b c hab
  have hMv : Mval [⟨a,b,c⟩] = a + b + 1 := by show Hnat [⟨a,b,c⟩] + 1 = a + b + 1; rw [hH]
  have hgn : gnat [⟨a,b,c⟩] = a + b - c := gnat_dpos a b c hab
  intro n hn1 hn2
  have hn1' : a + b + 1 ≤ n := by omega
  have hn2' : n ≤ 2 * (a + b) + (a + b - c) := by omega
  rw [hgn]
  have dd := descToOnes_pos a b c ha2 hb2 hac hbc hab hc3 (n + (a + b - c)) (by omega) (by omega)
  rw [show n + (a + b - c) - (a + b - c) = n from by omega] at dd
  exact reach_trans dd (gatherBig a b c ha2 hb2 n (by omega))

/-- **Full unconditional sufficiency for `a + b > c`** with legs in `[2, c)` and
    `2(a+b)+2 ≤ 3c` (the single-cluster family — e.g. `3+3=5`, `3+4=6`, `5+5=8`).
    Both pumps proved: `climb_dpos` and `baseD_dpos`. -/
theorem single_sufficiency_dpos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) (hc3 : 2 * (a + b) + 2 ≤ 3 * c) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  single_sufficiency_of_base a b c (by omega) (by omega) (by omega) (by omega)
    (baseC_dpos a b c ha2 hb2 hac hbc hab)
    (baseD_dpos a b c ha2 hb2 hac hbc hab hc3)

/-- The lie `3 + 3 = 5` is completely solvable above `M = 7`: every `s,t ≥ 7`
    (here `g = 1`, so no parity constraint) are interreachable. -/
theorem solvable_3_3_5 {s t : Nat} (hs : 7 ≤ s) (ht : 7 ≤ t) :
    Reach [⟨3,3,5⟩] [s] [t] :=
  single_sufficiency_dpos 3 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s t hs ht (by
      have : gz [⟨3,3,5⟩] = 1 := by decide
      rw [this]; exact ⟨(t : Int) - s, by omega⟩)

end YaStupid

-- Trust check: these print the axiom dependencies (should be the standard
-- [propext, Classical.choice, Quot.sound] — and crucially NOT `sorryAx`).
#print axioms YaStupid.reach_congr
#print axioms YaStupid.classic_trap
#print axioms YaStupid.cfg222_5_to_7
#print axioms YaStupid.classic_21_to_19
#print axioms YaStupid.sufficiency_of_pumps
#print axioms YaStupid.classic_42_to_44
#print axioms YaStupid.classic_sufficiency
#print axioms YaStupid.single_sufficiency_of_base

#print axioms YaStupid.scatterClean
#print axioms YaStupid.getUnits
#print axioms YaStupid.mergeUnitsHi
#print axioms YaStupid.gather
#print axioms YaStupid.climbCleanLow
#print axioms YaStupid.climb2cm1
#print axioms YaStupid.climb2c
#print axioms YaStupid.baseC_dneg
#print axioms YaStupid.climb_dneg

#print axioms YaStupid.gatherBig
#print axioms YaStupid.loseG
#print axioms YaStupid.descDrop
#print axioms YaStupid.baseD_dneg
#print axioms YaStupid.single_sufficiency_dneg
#print axioms YaStupid.classic_sufficiency_symbolic

#print axioms YaStupid.mergeUnitsLow
#print axioms YaStupid.climbCleanLow_pos
#print axioms YaStupid.descendCleanLow_pos
#print axioms YaStupid.climb_2c_pos
#print axioms YaStupid.baseC_dpos
#print axioms YaStupid.climb_dpos

#print axioms YaStupid.unlockC
#print axioms YaStupid.loseGpos
#print axioms YaStupid.descToOnes_pos
#print axioms YaStupid.baseD_dpos
namespace YaStupid

/-! ### The `min(a,b) = 1` edge of `a + b < c`

With `a = 1` and `b ≥ 2` the forbidden pair is `{1, b}`, so `gatherBig`'s `+1`
accumulator jams at `b → b+1` (merging `{b,1}`).  The climb side is unaffected (it
only builds legs `≤ max(a,b) = b` via the capped `gather`, and reels onto `c > b`
via `mergeUnitsHi`).  Descend only needs to *build* values `≥ b+2` (the harvested
`c > a+b = b+1`, and targets `n ≥ M = c+1`), which `gatherMin1` does by skipping the
forbidden `b+1`: build `[b]` and a spare `[2]`, merge to `b+2`, then reel ones on. -/

/-- Build any `v ≥ b+2` from `v` ones when `a = 1, b ≥ 2`, dodging the only
    forbidden merge `{1,b}` by jumping `b → b+2` through a spare `2`. -/
theorem gatherMin1 (a b c : Nat) (ha1 : a = 1) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ v, b + 2 ≤ v → Reach [⟨a,b,c⟩] (List.replicate v 1) [v] := by
  intro v hv
  have gB : Reach [⟨a,b,c⟩] (List.replicate v 1) (b :: List.replicate (v - b) 1) :=
    gatherPrefix a b c b v (by omega) (by omega) (by omega)
  have g2 : Reach [⟨a,b,c⟩] (List.replicate (v - b) 1) (2 :: List.replicate (v - b - 2) 1) :=
    gatherPrefix a b c 2 (v - b) (by omega) (by omega) (by omega)
  have s2 : Reach [⟨a,b,c⟩] (b :: List.replicate (v - b) 1)
      (b :: 2 :: List.replicate (v - b - 2) 1) := by
    have := reach_frame_left [b] g2; simpa using this
  have s3 : Reach [⟨a,b,c⟩] (b :: 2 :: List.replicate (v - b - 2) 1)
      ((b + 2) :: List.replicate (v - b - 2) 1) := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩]:Config), ¬ ((f.a = b ∧ f.b = 2) ∨ (f.a = 2 ∧ f.b = b)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move (List.replicate (v - b - 2) 1) (Local.nmerge b 2 hcc)
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s4 : Reach [⟨a,b,c⟩] ((b + 2) :: List.replicate (v - b - 2) 1) [(b + 2) + (v - b - 2)] :=
    mergeUnitsHi a b c (v - b - 2) (b + 2) (by omega)
  have e : (b + 2) + (v - b - 2) = v := by omega
  rw [e] at s4
  exact reach_trans gB (reach_trans s2 (reach_trans s3 s4))

/-- `loseG` for the `a = 1` edge: build the harvested `c` with `gatherMin1`. -/
theorem loseGmin1 (a b c : Nat) (ha1 : a = 1) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ m, c ≤ m → Reach [⟨a,b,c⟩] (List.replicate m 1) (List.replicate (m - (c - a - b)) 1) := by
  intro m hm
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherMin1 a b c ha1 hb2 hab c (by omega)
  have hsplitrep : List.replicate m (1:Nat) = List.replicate c 1 ++ List.replicate (m - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨a,b,c⟩] (List.replicate m 1) (c :: List.replicate (m - c) 1) := by
    rw [hsplitrep]; have := reach_frame (List.replicate (m - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (c :: List.replicate (m - c) 1) (a :: b :: List.replicate (m - c) 1) := by
    have hm2 := reach_move (List.replicate (m - c) 1)
      (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm2
  have sca : Reach [⟨a,b,c⟩] [a] (List.replicate a 1) := scatterClean a b c a (by omega) (by omega)
  have scb : Reach [⟨a,b,c⟩] [b] (List.replicate b 1) := scatterClean a b c b (by omega) (by omega)
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (m - c) 1)
      (List.replicate a 1 ++ (b :: List.replicate (m - c) 1)) := by
    have := reach_frame (b :: List.replicate (m - c) 1) sca; simpa using this
  have s4 : Reach [⟨a,b,c⟩] (List.replicate a 1 ++ (b :: List.replicate (m - c) 1))
      (List.replicate a 1 ++ (List.replicate b 1 ++ List.replicate (m - c) 1)) := by
    have := reach_frame_left (List.replicate a 1) (reach_frame (List.replicate (m - c) 1) scb)
    simpa using this
  have ecat : List.replicate a (1:Nat) ++ (List.replicate b 1 ++ List.replicate (m - c) 1)
      = List.replicate (m - (c - a - b)) 1 := by
    rw [replicate_one_add, replicate_one_add]; congr 1; omega
  rw [ecat] at s4
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))

/-- `descDrop` for the `a = 1` edge: clean values use `loseGmin1`; the cluster
    values reuse the (leg-agnostic) boundary lemmas. -/
theorem descDropMin1 (a b c : Nat) (ha1 : a = 1) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ m, c + 1 + (c - a - b) ≤ m → m ≤ 2 * c + 2 * (c - a - b) →
      Reach [⟨a,b,c⟩] [m] (List.replicate (m - (c - a - b)) 1) := by
  intro m h1 h2
  by_cases hA : m ≤ 2 * c - 2
  · exact reach_trans (getUnits a b c m (by omega) hA) (loseGmin1 a b c ha1 hb2 hab m (by omega))
  · by_cases hB : 2 * c + 2 ≤ m
    · -- high range: one split lands both halves in [c+1, 2c-2] (uses a+b ≥ 2)
      have hsplit : Reach [⟨a,b,c⟩] [m] [m / 2, (m + 1) / 2] :=
        reach_move [] (Local.nsplit m (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
      have step1 := reach_frame [(m + 1) / 2] (getUnits a b c (m / 2) (by omega) (by omega))
      have step2 := reach_frame_left (List.replicate (m / 2) 1)
        (getUnits a b c ((m + 1) / 2) (by omega) (by omega))
      have hcat : List.replicate (m / 2) 1 ++ List.replicate ((m + 1) / 2) 1 = List.replicate m 1 := by
        rw [replicate_one_add]; congr 1; omega
      rw [hcat] at step2
      exact reach_trans (reach_trans hsplit (reach_trans step1 step2))
        (loseGmin1 a b c ha1 hb2 hab m (by omega))
    · have hcase : m = 2 * c - 1 ∨ m = 2 * c ∨ m = 2 * c + 1 := by omega
      rcases hcase with h | h | h
      · rw [h]; exact descDrop_2cm1 a b c (by omega) (by omega) hab
      · rw [h]; exact descDrop_2c a b c (by omega) (by omega) hab
      · rw [h]; exact descDrop_2cp1 a b c (by omega) (by omega) hab

/-- The descend base for the `a = 1` edge. -/
theorem baseD_dneg_min1 (a b c : Nat) (ha1 : a = 1) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ n, Mval [⟨a,b,c⟩] ≤ n → n ≤ 2 * Hnat [⟨a,b,c⟩] + gnat [⟨a,b,c⟩] →
      Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n] := by
  have hH : Hnat [⟨a,b,c⟩] = c := Hnat_dneg a b c hab
  have hMv : Mval [⟨a,b,c⟩] = c + 1 := by show Hnat [⟨a,b,c⟩] + 1 = c + 1; rw [hH]
  have hgn : gnat [⟨a,b,c⟩] = c - a - b := gnat_dneg a b c hab
  intro n hn1 hn2
  have hn1' : c + 1 ≤ n := by omega
  have hn2' : n ≤ 2 * c + (c - a - b) := by omega
  rw [hgn]
  have dd := descDropMin1 a b c ha1 hb2 hab (n + (c - a - b)) (by omega) (by omega)
  rw [show n + (c - a - b) - (c - a - b) = n from by omega] at dd
  exact reach_trans dd (gatherMin1 a b c ha1 hb2 hab n (by omega))

/-- **Full sufficiency for the `min(a,b) = 1` edge of `a + b < c`** (`a = 1`,
    `b ≥ 2`).  Together with the `2 ≤ a, b` case, this closes **all** of `a + b < c`
    except the doubly-degenerate `a = b = 1` (where ones cannot merge at all). -/
theorem single_sufficiency_dneg_min1 (a b c : Nat) (ha1 : a = 1) (hb2 : 2 ≤ b) (hab : a + b < c) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  single_sufficiency_of_base a b c (by omega) (by omega) (by omega) (by omega)
    (baseC_dneg a b c (by omega) (by omega) hab)
    (baseD_dneg_min1 a b c ha1 hb2 hab)

/-- The lie `1 + 2 = 5` (a `min(a,b)=1` instance) is completely solvable above
    `M = 6`: every `s,t ≥ 6` with `2 ∣ (t−s)` are interreachable. -/
theorem solvable_1_2_5 {s t : Nat} (hs : 6 ≤ s) (ht : 6 ≤ t)
    (h : (2:Int) ∣ ((t:Int) - s)) : Reach [⟨1,2,5⟩] [s] [t] :=
  single_sufficiency_dneg_min1 1 2 5 rfl (by decide) (by decide) s t hs ht (by
    have : gz [⟨1,2,5⟩] = 2 := by decide
    rw [this]; exact h)

end YaStupid

namespace YaStupid

/-! ### A uniform hub for `a+b>c` with legs `< c` (all cluster structures)

Instead of per-cluster constructions, route everything through an all-ones *hub*.
Because both legs are `< c`, every ball scatters to ones: splitting strictly
reduces the max value, and the forced `c → {a,b}` lands below `c`.  The resulting
one-count `r` is path-dependent but satisfies `r ≥ v` and (via `reach_dvd`)
`g ∣ (r−v)`.  Then `loseGpos`/`gainGpos` walk between one-piles in steps of `g`,
and `gatherBig` rebuilds the target.  No `2(a+b)+2 ≤ 3c` restriction. -/

theorem total_replicate_one : ∀ r, total (List.replicate r 1) = r := by
  intro r; induction r with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, total_cons, ih]; omega

/-- Scatter any ball to *some* all-ones pile (legs `< c`). -/
theorem scatterRaw_dpos (a b c : Nat) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) : ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨a,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv1
    by_cases hvc : v = c
    · rw [hvc]
      obtain ⟨ra, hra1, hrar⟩ := ih a (by omega) (by omega)
      obtain ⟨rb, hrb1, hrbr⟩ := ih b (by omega) (by omega)
      refine ⟨ra + rb, by omega, ?_⟩
      have hfs : Reach [⟨a,b,c⟩] [c] [a, b] := by
        have hm := reach_move [] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
          (List.Perm.refl _) (Reach.refl _); simpa using hm
      have st1 : Reach [⟨a,b,c⟩] [a, b] (List.replicate ra 1 ++ [b]) := by
        have := reach_frame [b] hrar; simpa using this
      have st2 : Reach [⟨a,b,c⟩] (List.replicate ra 1 ++ [b])
          (List.replicate ra 1 ++ List.replicate rb 1) := by
        have := reach_frame_left (List.replicate ra 1) hrbr; simpa using this
      rw [replicate_one_add] at st2
      exact reach_trans hfs (reach_trans st1 st2)
    · by_cases hv2 : 2 ≤ v
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        obtain ⟨r2, hr21, hr2r⟩ := ih ((v + 1) / 2) (by omega) (by omega)
        refine ⟨r1 + r2, by omega, ?_⟩
        have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have st1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have st2 : Reach [⟨a,b,c⟩] (List.replicate r1 1 ++ [(v + 1) / 2])
            (List.replicate r1 1 ++ List.replicate r2 1) := by
          have := reach_frame_left (List.replicate r1 1) hr2r; simpa using this
        rw [replicate_one_add] at st2
        exact reach_trans hns (reach_trans st1 st2)
      · refine ⟨1, by omega, ?_⟩
        have : v = 1 := by omega
        rw [this]; exact Reach.refl _

/-- Raise a pile of ones by `g` (`d>0`): build a `c`, false-split it, scatter the
    legs back.  `1^K → 1^(K+g)` for `K ≥ c`. -/
theorem gainGpos (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) :
    ∀ K, c ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + (a + b - c)) 1) := by
  intro K hK
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherBig a b c ha2 hb2 c (by omega)
  have hsplitrep : List.replicate K (1:Nat) = List.replicate c 1 ++ List.replicate (K - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨a,b,c⟩] (List.replicate K 1) (c :: List.replicate (K - c) 1) := by
    rw [hsplitrep]; have := reach_frame (List.replicate (K - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (c :: List.replicate (K - c) 1) (a :: b :: List.replicate (K - c) 1) := by
    have hm2 := reach_move (List.replicate (K - c) 1)
      (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm2
  have sca : Reach [⟨a,b,c⟩] [a] (List.replicate a 1) := scatterClean a b c a (by omega) (by omega)
  have scb : Reach [⟨a,b,c⟩] [b] (List.replicate b 1) := scatterClean a b c b (by omega) (by omega)
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (K - c) 1)
      (List.replicate a 1 ++ (b :: List.replicate (K - c) 1)) := by
    have := reach_frame (b :: List.replicate (K - c) 1) sca; simpa using this
  have s4 : Reach [⟨a,b,c⟩] (List.replicate a 1 ++ (b :: List.replicate (K - c) 1))
      (List.replicate a 1 ++ (List.replicate b 1 ++ List.replicate (K - c) 1)) := by
    have := reach_frame_left (List.replicate a 1) (reach_frame (List.replicate (K - c) 1) scb)
    simpa using this
  have ecat : List.replicate a (1:Nat) ++ (List.replicate b 1 ++ List.replicate (K - c) 1)
      = List.replicate (K + (a + b - c)) 1 := by
    rw [replicate_one_add, replicate_one_add]; congr 1; omega
  rw [ecat] at s4
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))

/-- Walk a one-pile UP by `k·g`. -/
theorem onesUpK (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) :
    ∀ k K, c ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + k * (a + b - c)) 1) := by
  intro k
  induction k with
  | zero => intro K hK; rw [Nat.zero_mul, Nat.add_zero]; exact Reach.refl _
  | succ k ih =>
    intro K hK
    have step := gainGpos a b c ha2 hb2 hac hbc hab K hK
    have hrec := ih (K + (a + b - c)) (by omega)
    rw [Nat.succ_mul]
    rw [show K + (a + b - c) + k * (a + b - c) = K + (k * (a + b - c) + (a + b - c)) from by omega] at hrec
    exact reach_trans step hrec

/-- Walk a one-pile DOWN by `k·g` (staying `≥ a+b+1`). -/
theorem onesDownK (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hac : a < c) (hbc : b < c)
    (hab : c < a + b) :
    ∀ k K, a + b + 1 + k * (a + b - c) ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - k * (a + b - c)) 1) := by
  intro k
  induction k with
  | zero => intro K hK; rw [Nat.zero_mul, Nat.sub_zero]; exact Reach.refl _
  | succ k ih =>
    intro K hK
    have hsm : (k + 1) * (a + b - c) = k * (a + b - c) + (a + b - c) := Nat.succ_mul k (a + b - c)
    have step := loseGpos a b c ha2 hb2 hac hbc hab K (by omega)
    have hrec := ih (K - (a + b - c)) (by omega)
    rw [Nat.succ_mul]
    rw [show K - (a + b - c) - k * (a + b - c) = K - (k * (a + b - c) + (a + b - c)) from by omega] at hrec
    exact reach_trans step hrec

/-- **Full unconditional sufficiency for `a + b > c` with legs in `[2, c)`** — the
    entire family, *no* single-cluster restriction (so `4+4=5`, `5+5=7`, … are now
    covered).  Route through the all-ones hub: scatter `[s]` to `1^r`, walk the pile
    to `1^t` in steps of `g`, rebuild `[t]`. -/
theorem single_sufficiency_dpos_full (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hac : a < c) (hbc : b < c) (hab : c < a + b) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  intro s t hs ht hg
  have hH : Hnat [⟨a,b,c⟩] = a + b := Hnat_dpos a b c hab
  have hMv : Mval [⟨a,b,c⟩] = a + b + 1 := by show Hnat [⟨a,b,c⟩] + 1 = a + b + 1; rw [hH]
  have hgz : gz [⟨a,b,c⟩] = ((a + b - c : Nat) : Int) := by
    show ((gnat [⟨a,b,c⟩] : Nat) : Int) = _; rw [gnat_dpos a b c hab]
  have hs' : a + b + 1 ≤ s := by omega
  have ht' : a + b + 1 ≤ t := by omega
  obtain ⟨r, hsr, hreach⟩ := scatterRaw_dpos a b c (by omega) (by omega) hac hbc hab s (by omega)
  have hr' : a + b + 1 ≤ r := by omega
  -- residue of the scatter: g ∣ (r − s)
  have hrs : gz [⟨a,b,c⟩] ∣ ((r : Int) - s) := by
    have hd := reach_dvd hreach
    rwa [total_replicate_one, show total [s] = s from by simp] at hd
  -- hence g ∣ (t − r)
  obtain ⟨p, hp⟩ := hg
  obtain ⟨q, hq⟩ := hrs
  have htr : gz [⟨a,b,c⟩] ∣ ((t : Int) - r) := ⟨p - q, by rw [Int.mul_sub, ← hp, ← hq]; omega⟩
  -- walk the one-pile from r to t
  have hpile : Reach [⟨a,b,c⟩] (List.replicate r 1) (List.replicate t 1) := by
    rcases Nat.le_total r t with hle | hge
    · have hnd : (a + b - c) ∣ (t - r) := by
        have h1 : ((a + b - c : Nat) : Int) ∣ ((t - r : Nat) : Int) := by
          rw [Int.natCast_sub hle, ← hgz]; exact htr
        exact Int.natCast_dvd_natCast.mp h1
      obtain ⟨k, hk⟩ := hnd
      have hu := onesUpK a b c ha2 hb2 hac hbc hab k r (by omega)
      rwa [show r + k * (a + b - c) = t from by rw [Nat.mul_comm]; omega] at hu
    · have hnd : (a + b - c) ∣ (r - t) := by
        have h2 : ((a + b - c : Nat) : Int) ∣ ((r : Int) - t) := by
          have hneg := dvd_neg' htr
          rw [show -((t:Int) - r) = (r:Int) - t from by omega] at hneg
          rwa [hgz] at hneg
        have h3 : ((a + b - c : Nat) : Int) ∣ ((r - t : Nat) : Int) := by
          rw [Int.natCast_sub hge]; exact h2
        exact Int.natCast_dvd_natCast.mp h3
      obtain ⟨k, hk⟩ := hnd
      have hd := onesDownK a b c ha2 hb2 hac hbc hab k r (by rw [Nat.mul_comm]; omega)
      rwa [show r - k * (a + b - c) = t from by rw [Nat.mul_comm]; omega] at hd
  exact reach_trans hreach (reach_trans hpile (gatherBig a b c ha2 hb2 t (by omega)))

/-- The lie `4 + 4 = 5` — a genuinely **multi-cluster** instance (both `2c=10` and
    `4c=20` sit in the descend range) — is completely solvable above `M = 9`. -/
theorem solvable_4_4_5 {s t : Nat} (hs : 9 ≤ s) (ht : 9 ≤ t)
    (h : (3:Int) ∣ ((t:Int) - s)) : Reach [⟨4,4,5⟩] [s] [t] :=
  single_sufficiency_dpos_full 4 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    s t hs ht (by have : gz [⟨4,4,5⟩] = 3 := by decide
                  rw [this]; exact h)

#print axioms YaStupid.scatterRaw_dpos
#print axioms YaStupid.single_sufficiency_dpos_full
#print axioms YaStupid.solvable_4_4_5

end YaStupid

namespace YaStupid

/-! ### The doubly-degenerate edge `a = b = 1` (`a + b < c`)

From a pile of pure ones the only merge is the forced `{1,1} → c`, so nothing can
be built from ones and a one-pile can never descend.  The fix: keep a **2-seed**.
A `2` survives any clean scatter, and `mergeUnitsHi` (base `2 > max(1,1)`) reels
ones onto it, so any value is buildable from `[2] + ones`.  Descend then reads:
build `[2c]` from a 2-seed, split to `[c,c]`, false-split one `c` (losing `g`),
and reel everything onto the other `c`. -/

/-- A move that may permute its *result* (the generic `Step`, not just `reach_move`'s
    `rfl` result). -/
theorem reach_move' {cfg : Config} {a ain aout : List Nat} (rest : List Nat)
    (hl : Local cfg ain aout) (hp : a.Perm (ain ++ rest)) {b bb : List Nat}
    (hpb : bb.Perm (aout ++ rest)) (hr : Reach cfg bb b) : Reach cfg a b :=
  Reach.step ⟨ain, aout, rest, hl, hp, hpb⟩ hr

/-- Scatter `[v]` (with `v < c`) to ones but **keep one `2` at the front**. -/
theorem keep2 (c : Nat) (hc3 : 3 ≤ c) :
    ∀ v, 2 ≤ v → v < c → Reach [⟨1,1,c⟩] [v] (2 :: List.replicate (v - 2) 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv2 hvc
    rcases Nat.lt_or_ge v 4 with hsmall | hge
    · rcases Nat.lt_or_ge v 3 with h2 | h3
      · have hv : v = 2 := by omega
        subst hv; exact Reach.refl _
      · have hv : v = 3 := by omega
        subst hv
        -- [3] → nsplit → [1,2], permute result to [2,1] = 2 :: replicate 1 1
        exact reach_move' [] (Local.nsplit 3 (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _)
          (by decide) (Reach.refl _)
    · have hsp : Reach [⟨1,1,c⟩] [v] [v / 2, (v + 1) / 2] :=
        reach_move [] (Local.nsplit v (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
      have s1 : Reach [⟨1,1,c⟩] [v / 2, (v + 1) / 2]
          ((2 :: List.replicate (v / 2 - 2) 1) ++ [(v + 1) / 2]) := by
        have := reach_frame [(v + 1) / 2] (ih (v / 2) (by omega) (by omega) (by omega))
        simpa using this
      have s2 : Reach [⟨1,1,c⟩] ((2 :: List.replicate (v / 2 - 2) 1) ++ [(v + 1) / 2])
          ((2 :: List.replicate (v / 2 - 2) 1) ++ List.replicate ((v + 1) / 2) 1) :=
        reach_frame_left _ (scatterClean 1 1 c ((v + 1) / 2) (by omega) (by omega))
      have e : (2 :: List.replicate (v / 2 - 2) 1) ++ List.replicate ((v + 1) / 2) 1
          = 2 :: List.replicate (v - 2) 1 := by
        rw [List.cons_append, replicate_one_add]; congr 2; omega
      rw [e] at s2
      exact reach_trans hsp (reach_trans s1 s2)

/-- Scatter `[v]` (with `c+1 ≤ v ≤ 2c−2`) to ones, keeping one `2` at the front. -/
theorem keep2hi (c : Nat) (hc3 : 3 ≤ c) :
    ∀ v, c + 1 ≤ v → v ≤ 2 * c - 2 → Reach [⟨1,1,c⟩] [v] (2 :: List.replicate (v - 2) 1) := by
  intro v h1 h2
  have hsp : Reach [⟨1,1,c⟩] [v] [v / 2, (v + 1) / 2] :=
    reach_move [] (Local.nsplit v (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have s1 : Reach [⟨1,1,c⟩] [v / 2, (v + 1) / 2]
      ((2 :: List.replicate (v / 2 - 2) 1) ++ [(v + 1) / 2]) := by
    have := reach_frame [(v + 1) / 2] (keep2 c hc3 (v / 2) (by omega) (by omega))
    simpa using this
  have s2 : Reach [⟨1,1,c⟩] ((2 :: List.replicate (v / 2 - 2) 1) ++ [(v + 1) / 2])
      ((2 :: List.replicate (v / 2 - 2) 1) ++ List.replicate ((v + 1) / 2) 1) :=
    reach_frame_left _ (scatterClean 1 1 c ((v + 1) / 2) (by omega) (by omega))
  have e : (2 :: List.replicate (v / 2 - 2) 1) ++ List.replicate ((v + 1) / 2) 1
      = 2 :: List.replicate (v - 2) 1 := by
    rw [List.cons_append, replicate_one_add]; congr 2; omega
  rw [e] at s2
  exact reach_trans hsp (reach_trans s1 s2)

/-- Reach a single 2-seed plus ones, `[m] → 2 :: 1^(m-2)`, for `m ∈ [2c+2, 4c-4]`
    (both halves land in `[c+1, 2c-2]`). -/
theorem reach2seed (c : Nat) (hc3 : 3 ≤ c) :
    ∀ m, 2 * c + 2 ≤ m → m ≤ 4 * c - 4 → Reach [⟨1,1,c⟩] [m] (2 :: List.replicate (m - 2) 1) := by
  intro m h1 h2
  have hsp : Reach [⟨1,1,c⟩] [m] [m / 2, (m + 1) / 2] :=
    reach_move [] (Local.nsplit m (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have s1 : Reach [⟨1,1,c⟩] [m / 2, (m + 1) / 2]
      ((2 :: List.replicate (m / 2 - 2) 1) ++ [(m + 1) / 2]) := by
    have := reach_frame [(m + 1) / 2] (keep2hi c hc3 (m / 2) (by omega) (by omega))
    simpa using this
  have s2 : Reach [⟨1,1,c⟩] ((2 :: List.replicate (m / 2 - 2) 1) ++ [(m + 1) / 2])
      ((2 :: List.replicate (m / 2 - 2) 1) ++ List.replicate ((m + 1) / 2) 1) :=
    reach_frame_left _ (getUnits 1 1 c ((m + 1) / 2) (by omega) (by omega))
  have e : (2 :: List.replicate (m / 2 - 2) 1) ++ List.replicate ((m + 1) / 2) 1
      = 2 :: List.replicate (m - 2) 1 := by
    rw [List.cons_append, replicate_one_add]; congr 2; omega
  rw [e] at s2
  exact reach_trans hsp (reach_trans s1 s2)

/-- Descend the cluster value `2c−1` (`a=b=1`): split to `[c−1, c]`, false-split
    the `c`, reel the two ones onto `c−1`. -/
theorem descA_2cm1 (c : Nat) (hc3 : 3 ≤ c) : Reach [⟨1,1,c⟩] [2 * c - 1] [c + 1] := by
  have hsp : Reach [⟨1,1,c⟩] [2 * c - 1] [(2*c-1)/2, (2*c-1+1)/2] :=
    reach_move [] (Local.nsplit (2*c-1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  rw [show (2*c-1)/2 = c - 1 from by omega, show (2*c-1+1)/2 = c from by omega] at hsp
  have hmu := mergeUnitsHi 1 1 c 2 (c - 1) (by omega)
  rw [show (c - 1) + 2 = c + 1 from by omega] at hmu
  exact reach_trans hsp (reach_move' [c - 1] (Local.fsplit ⟨1,1,c⟩ (List.mem_singleton.2 rfl))
    (List.Perm.swap c (c - 1) []) (perm_c_ab 1 1 (c - 1) []) hmu)

/-- Descend the stuck value `2c` (`a=b=1`): `2c → [c,c]`, false-split one `c`, reel
    the two ones onto the other `c`. -/
theorem descA_2c (c : Nat) (hc3 : 3 ≤ c) : Reach [⟨1,1,c⟩] [2 * c] [c + 2] := by
  have hsp : Reach [⟨1,1,c⟩] [2 * c] [(2*c)/2, (2*c+1)/2] :=
    reach_move [] (Local.nsplit (2*c) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  rw [show (2*c)/2 = c from by omega, show (2*c+1)/2 = c from by omega] at hsp
  have hmu := mergeUnitsHi 1 1 c 2 c (by omega)
  exact reach_trans hsp (reach_move' [c] (Local.fsplit ⟨1,1,c⟩ (List.mem_singleton.2 rfl))
    (List.Perm.refl _) (perm_c_ab 1 1 c []) hmu)

/-- Descend the cluster value `2c+1` (`a=b=1`). -/
theorem descA_2cp1 (c : Nat) (hc3 : 3 ≤ c) : Reach [⟨1,1,c⟩] [2 * c + 1] [c + 3] := by
  have hsp : Reach [⟨1,1,c⟩] [2 * c + 1] [(2*c+1)/2, (2*c+1+1)/2] :=
    reach_move [] (Local.nsplit (2*c+1) (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  rw [show (2*c+1)/2 = c from by omega, show (2*c+1+1)/2 = c + 1 from by omega] at hsp
  have hmu := mergeUnitsHi 1 1 c 2 (c + 1) (by omega)
  rw [show (c + 1) + 2 = c + 3 from by omega] at hmu
  exact reach_trans hsp (reach_move' [c + 1] (Local.fsplit ⟨1,1,c⟩ (List.mem_singleton.2 rfl))
    (List.Perm.refl _) (perm_c_ab 1 1 (c + 1) []) hmu)

/-- Descend any `m ∈ [2c+2, 4c-4]` (`a=b=1`): get a 2-seed, build `[2c]`, split to
    `[c,c]`, false-split one `c`, reel everything onto the other. -/
theorem descA_hi (c : Nat) (hc3 : 3 ≤ c) :
    ∀ m, 2 * c + 2 ≤ m → m ≤ 4 * c - 4 → Reach [⟨1,1,c⟩] [m] [m - (c - 2)] := by
  intro m h1 h2
  have s_seed := reach2seed c hc3 m h1 h2
  have hsplitrep : (2 :: List.replicate (m - 2) 1)
      = (2 :: List.replicate (2*c - 2) 1) ++ List.replicate (m - 2*c) 1 := by
    rw [List.cons_append, replicate_one_add]; congr 2; omega
  have s_build : Reach [⟨1,1,c⟩] (2 :: List.replicate (m - 2) 1)
      (2 * c :: List.replicate (m - 2*c) 1) := by
    rw [hsplitrep]
    have hmu := mergeUnitsHi 1 1 c (2*c - 2) 2 (by omega)
    rw [show 2 + (2*c - 2) = 2 * c from by omega] at hmu
    have := reach_frame (List.replicate (m - 2*c) 1) hmu; simpa using this
  have s_split : Reach [⟨1,1,c⟩] (2 * c :: List.replicate (m - 2*c) 1)
      (c :: c :: List.replicate (m - 2*c) 1) := by
    have hm := reach_move (List.replicate (m - 2*c) 1)
      (Local.nsplit (cfg := [⟨1,1,c⟩]) (2*c) (by omega)
        (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    rw [show (2*c)/2 = c from by omega, show (2*c+1)/2 = c from by omega] at hm
    simpa using hm
  have s_fire : Reach [⟨1,1,c⟩] (c :: c :: List.replicate (m - 2*c) 1) [m - (c - 2)] := by
    have hmu := mergeUnitsHi 1 1 c (m - 2*c + 2) c (by omega)
    rw [show c + (m - 2*c + 2) = m - (c - 2) from by omega] at hmu
    refine reach_move' (c :: List.replicate (m - 2*c) 1)
      (Local.fsplit ⟨1,1,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) ?_ hmu
    rw [show m - 2*c + 2 = (m - 2*c) + 1 + 1 from by omega, List.replicate_succ, List.replicate_succ]
    exact perm_c_ab 1 1 c (List.replicate (m - 2*c) 1)
  exact reach_trans s_seed (reach_trans s_build (reach_trans s_split s_fire))

/-- **The descend base for `a=b=1`.** -/
theorem baseD_a11 (c : Nat) (hc3 : 3 ≤ c) :
    ∀ n, Mval [⟨1,1,c⟩] ≤ n → n ≤ 2 * Hnat [⟨1,1,c⟩] + gnat [⟨1,1,c⟩] →
      Reach [⟨1,1,c⟩] [n + gnat [⟨1,1,c⟩]] [n] := by
  have hH : Hnat [⟨1,1,c⟩] = c := by show max (max (1 + 1) c) 0 = c; omega
  have hgn : gnat [⟨1,1,c⟩] = c - 2 := by rw [gnat_single]; omega
  have hMv : Mval [⟨1,1,c⟩] = c + 1 := by show Hnat [⟨1,1,c⟩] + 1 = c + 1; rw [hH]
  intro n hn1 hn2
  have hn1' : c + 1 ≤ n := by omega
  have hn2' : n ≤ 2 * c + (c - 2) := by omega
  rw [hgn]
  by_cases he1 : n = c + 1
  · rw [he1, show (c + 1) + (c - 2) = 2 * c - 1 from by omega]; exact descA_2cm1 c hc3
  · by_cases he2 : n = c + 2
    · rw [he2, show (c + 2) + (c - 2) = 2 * c from by omega]; exact descA_2c c hc3
    · by_cases he3 : n = c + 3
      · rw [he3, show (c + 3) + (c - 2) = 2 * c + 1 from by omega]; exact descA_2cp1 c hc3
      · have := descA_hi c hc3 (n + (c - 2)) (by omega) (by omega)
        rwa [show n + (c - 2) - (c - 2) = n from by omega] at this

/-- **Full sufficiency for `a = b = 1`** (`1 + 1 = c`, `c ≥ 3`).  This closes the
    last `a + b < c` family: solvability is now completely characterized for
    *every* single sum with `a + b < c`. -/
theorem single_sufficiency_a11 (c : Nat) (hc3 : 3 ≤ c) :
    ∀ s t, Mval [⟨1,1,c⟩] ≤ s → Mval [⟨1,1,c⟩] ≤ t →
      gz [⟨1,1,c⟩] ∣ ((t : Int) - s) → Reach [⟨1,1,c⟩] [s] [t] :=
  single_sufficiency_of_base 1 1 c (by omega) (by omega) (by omega) (by omega)
    (baseC_dneg 1 1 c (by omega) (by omega) (by omega))
    (baseD_a11 c hc3)

/-- The lie `1 + 1 = 5` is completely solvable above `M = 6`. -/
theorem solvable_1_1_5 {s t : Nat} (hs : 6 ≤ s) (ht : 6 ≤ t)
    (h : (3:Int) ∣ ((t:Int) - s)) : Reach [⟨1,1,5⟩] [s] [t] :=
  single_sufficiency_a11 5 (by decide) s t hs ht (by
    have : gz [⟨1,1,5⟩] = 3 := by decide
    rw [this]; exact h)

#print axioms YaStupid.descA_hi
#print axioms YaStupid.baseD_a11
#print axioms YaStupid.single_sufficiency_a11
#print axioms YaStupid.solvable_1_1_5

end YaStupid

#print axioms YaStupid.gatherMin1
#print axioms YaStupid.loseGmin1
#print axioms YaStupid.baseD_dneg_min1
#print axioms YaStupid.single_sufficiency_dneg_min1
#print axioms YaStupid.single_sufficiency_dpos
#print axioms YaStupid.solvable_3_3_5


namespace YaStupid

/-! ### The last open family: `a + b > c` with a leg `≥ c`

When `a + b > c` but a leg is `≥ c`, the all-ones hub of `single_sufficiency_dpos_full`
breaks at exactly one point: scattering the legs back to ones after the forced
`c → {a,b}`.  `scatterClean` requires `a < c`, `b < c`, and the greedy max-value
measure can genuinely *loop* (`c → {a,b}` raises the max when a leg `> c`), so no
single well-founded measure makes scatter terminate in general.

We isolate that obstruction as two hypotheses

  `la : Reach [⟨a,b,c⟩] [a] (1^a)`     `lb : Reach [⟨a,b,c⟩] [b] (1^b)`

— "each leg scatters to ones".  Every *other* hub ingredient (`gatherBig`,
`gatherPrefix`, `unlockC`) is already leg-`<c`-free, so conditional on `la, lb`
the entire sufficiency proof goes through for **any** legs.  These hypotheses are
free when both legs `< c` (just `scatterClean`), and dischargeable per config
whenever the legs do scatter (e.g. `2 + 10 = 7`, `lb` splits `10 → [5,5]`),
cleanly separating the solvable instances from the genuinely-looping ones
(`2 + 2 = 2`, where `2 → {2,2}` can never reach ones). -/

/-- `loseGpos` with the (unused) `a < c`, `b < c` dropped — drop `g` from a pile
    of ones using only `gatherPrefix`/`fmerge`/`unlockC`, all leg-`<c`-free.
    `1^K → 1^(K−g)` for `K ≥ a+b+1`. -/
theorem loseGposGen (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 3 ≤ c)
    (hab : c < a + b) :
    ∀ K, a + b + 1 ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - (a + b - c)) 1) := by
  intro K hK
  have ga : Reach [⟨a,b,c⟩] (List.replicate K 1) (a :: List.replicate (K - a) 1) :=
    gatherPrefix a b c a K (by omega) (by omega) (by omega)
  have gb : Reach [⟨a,b,c⟩] (List.replicate (K - a) 1) (b :: List.replicate (K - a - b) 1) :=
    gatherPrefix a b c b (K - a) (by omega) (by omega) (by omega)
  have s2 : Reach [⟨a,b,c⟩] (a :: List.replicate (K - a) 1)
      (a :: b :: List.replicate (K - a - b) 1) := by
    have := reach_frame_left [a] gb; simpa using this
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (K - a - b) 1)
      (c :: List.replicate (K - a - b) 1) := by
    have hm := reach_move (List.replicate (K - a - b) 1)
      (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s4 : Reach [⟨a,b,c⟩] (c :: List.replicate (K - a - b) 1)
      (List.replicate (c + (K - a - b)) 1) :=
    unlockC a b c ha2 hb2 hc3 (K - a - b) (by omega)
  have e : c + (K - a - b) = K - (a + b - c) := by omega
  rw [e] at s4
  exact reach_trans ga (reach_trans s2 (reach_trans s3 s4))

/-- `gainGpos` with the leg scatters supplied as hypotheses `la`, `lb` instead of
    `scatterClean` — so it holds for **any** legs.  `1^K → 1^(K+g)` for `K ≥ c`. -/
theorem gainGposGen (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 3 ≤ c) (hab : c < a + b)
    (la : Reach [⟨a,b,c⟩] [a] (List.replicate a 1))
    (lb : Reach [⟨a,b,c⟩] [b] (List.replicate b 1)) :
    ∀ K, c ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + (a + b - c)) 1) := by
  intro K hK
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherBig a b c ha2 hb2 c (by omega)
  have hsplitrep : List.replicate K (1:Nat) = List.replicate c 1 ++ List.replicate (K - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨a,b,c⟩] (List.replicate K 1) (c :: List.replicate (K - c) 1) := by
    rw [hsplitrep]; have := reach_frame (List.replicate (K - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (c :: List.replicate (K - c) 1) (a :: b :: List.replicate (K - c) 1) := by
    have hm2 := reach_move (List.replicate (K - c) 1)
      (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm2
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (K - c) 1)
      (List.replicate a 1 ++ (b :: List.replicate (K - c) 1)) := by
    have := reach_frame (b :: List.replicate (K - c) 1) la; simpa using this
  have s4 : Reach [⟨a,b,c⟩] (List.replicate a 1 ++ (b :: List.replicate (K - c) 1))
      (List.replicate a 1 ++ (List.replicate b 1 ++ List.replicate (K - c) 1)) := by
    have := reach_frame_left (List.replicate a 1) (reach_frame (List.replicate (K - c) 1) lb)
    simpa using this
  have ecat : List.replicate a (1:Nat) ++ (List.replicate b 1 ++ List.replicate (K - c) 1)
      = List.replicate (K + (a + b - c)) 1 := by
    rw [replicate_one_add, replicate_one_add]; congr 1; omega
  rw [ecat] at s4
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))

/-- Scatter any ball to *some* all-ones pile, using the leg scatters `la`, `lb` at
    the forced `c → {a,b}` step instead of recursing into the legs.  This makes the
    recursion strictly decreasing (halving on every non-`c` value), so it is
    well-founded for **any** legs — including legs `≥ c`. -/
theorem scatterRawClean (a b c : Nat) (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (hab : c < a + b)
    (la : Reach [⟨a,b,c⟩] [a] (List.replicate a 1))
    (lb : Reach [⟨a,b,c⟩] [b] (List.replicate b 1)) :
    ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨a,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv1
    by_cases hvc : v = c
    · rw [hvc]
      refine ⟨a + b, by omega, ?_⟩
      have hfs : Reach [⟨a,b,c⟩] [c] [a, b] := by
        have hm := reach_move [] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
          (List.Perm.refl _) (Reach.refl _); simpa using hm
      have st1 : Reach [⟨a,b,c⟩] [a, b] (List.replicate a 1 ++ [b]) := by
        have := reach_frame [b] la; simpa using this
      have st2 : Reach [⟨a,b,c⟩] (List.replicate a 1 ++ [b])
          (List.replicate a 1 ++ List.replicate b 1) := by
        have := reach_frame_left (List.replicate a 1) lb; simpa using this
      rw [replicate_one_add] at st2
      exact reach_trans hfs (reach_trans st1 st2)
    · by_cases hv2 : 2 ≤ v
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        obtain ⟨r2, hr21, hr2r⟩ := ih ((v + 1) / 2) (by omega) (by omega)
        refine ⟨r1 + r2, by omega, ?_⟩
        have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have st1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have st2 : Reach [⟨a,b,c⟩] (List.replicate r1 1 ++ [(v + 1) / 2])
            (List.replicate r1 1 ++ List.replicate r2 1) := by
          have := reach_frame_left (List.replicate r1 1) hr2r; simpa using this
        rw [replicate_one_add] at st2
        exact reach_trans hns (reach_trans st1 st2)
      · refine ⟨1, by omega, ?_⟩
        have : v = 1 := by omega
        rw [this]; exact Reach.refl _

/-- Walk a one-pile UP by `k·g` (conditional on `la`, `lb`). -/
theorem onesUpKGen (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 3 ≤ c) (hab : c < a + b)
    (la : Reach [⟨a,b,c⟩] [a] (List.replicate a 1))
    (lb : Reach [⟨a,b,c⟩] [b] (List.replicate b 1)) :
    ∀ k K, c ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + k * (a + b - c)) 1) := by
  intro k
  induction k with
  | zero => intro K hK; rw [Nat.zero_mul, Nat.add_zero]; exact Reach.refl _
  | succ k ih =>
    intro K hK
    have step := gainGposGen a b c ha2 hb2 hc3 hab la lb K hK
    have hrec := ih (K + (a + b - c)) (by omega)
    rw [Nat.succ_mul]
    rw [show K + (a + b - c) + k * (a + b - c) = K + (k * (a + b - c) + (a + b - c)) from by omega] at hrec
    exact reach_trans step hrec

/-- Walk a one-pile DOWN by `k·g`, staying `≥ a+b+1`. -/
theorem onesDownKGen (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 3 ≤ c) (hab : c < a + b) :
    ∀ k K, a + b + 1 + k * (a + b - c) ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - k * (a + b - c)) 1) := by
  intro k
  induction k with
  | zero => intro K hK; rw [Nat.zero_mul, Nat.sub_zero]; exact Reach.refl _
  | succ k ih =>
    intro K hK
    have hsm : (k + 1) * (a + b - c) = k * (a + b - c) + (a + b - c) := Nat.succ_mul k (a + b - c)
    have step := loseGposGen a b c ha2 hb2 hc3 hab K (by omega)
    have hrec := ih (K - (a + b - c)) (by omega)
    rw [Nat.succ_mul]
    rw [show K - (a + b - c) - k * (a + b - c) = K - (k * (a + b - c) + (a + b - c)) from by omega] at hrec
    exact reach_trans step hrec

/-- **Conditional sufficiency for `a + b > c` with *any* legs (including `≥ c`)**,
    given that each leg scatters to ones (`la`, `lb`).  Route through the all-ones
    hub: `scatterRawClean` sends `[s] → 1^r`, `onesUpKGen`/`onesDownKGen` walk the
    pile to `1^t` in steps of `g`, `gatherBig` rebuilds `[t]`.  Recovers
    `single_sufficiency_dpos_full` when both legs `< c` (then `la`, `lb` are free). -/
theorem single_sufficiency_legGE (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 3 ≤ c)
    (hab : c < a + b)
    (la : Reach [⟨a,b,c⟩] [a] (List.replicate a 1))
    (lb : Reach [⟨a,b,c⟩] [b] (List.replicate b 1)) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  intro s t hs ht hg
  have hH : Hnat [⟨a,b,c⟩] = a + b := Hnat_dpos a b c hab
  have hMv : Mval [⟨a,b,c⟩] = a + b + 1 := by show Hnat [⟨a,b,c⟩] + 1 = a + b + 1; rw [hH]
  have hgz : gz [⟨a,b,c⟩] = ((a + b - c : Nat) : Int) := by
    show ((gnat [⟨a,b,c⟩] : Nat) : Int) = _; rw [gnat_dpos a b c hab]
  have hs' : a + b + 1 ≤ s := by omega
  have ht' : a + b + 1 ≤ t := by omega
  obtain ⟨r, hsr, hreach⟩ := scatterRawClean a b c (by omega) (by omega) hab la lb s (by omega)
  have hr' : a + b + 1 ≤ r := by omega
  have hrs : gz [⟨a,b,c⟩] ∣ ((r : Int) - s) := by
    have hd := reach_dvd hreach
    rwa [total_replicate_one, show total [s] = s from by simp] at hd
  obtain ⟨p, hp⟩ := hg
  obtain ⟨q, hq⟩ := hrs
  have htr : gz [⟨a,b,c⟩] ∣ ((t : Int) - r) := ⟨p - q, by rw [Int.mul_sub, ← hp, ← hq]; omega⟩
  have hpile : Reach [⟨a,b,c⟩] (List.replicate r 1) (List.replicate t 1) := by
    rcases Nat.le_total r t with hle | hge
    · have hnd : (a + b - c) ∣ (t - r) := by
        have h1 : ((a + b - c : Nat) : Int) ∣ ((t - r : Nat) : Int) := by
          rw [Int.natCast_sub hle, ← hgz]; exact htr
        exact Int.natCast_dvd_natCast.mp h1
      obtain ⟨k, hk⟩ := hnd
      have hu := onesUpKGen a b c ha2 hb2 hc3 hab la lb k r (by omega)
      rwa [show r + k * (a + b - c) = t from by rw [Nat.mul_comm]; omega] at hu
    · have hnd : (a + b - c) ∣ (r - t) := by
        have h2 : ((a + b - c : Nat) : Int) ∣ ((r : Int) - t) := by
          have hneg := dvd_neg' htr
          rw [show -((t:Int) - r) = (r:Int) - t from by omega] at hneg
          rwa [hgz] at hneg
        have h3 : ((a + b - c : Nat) : Int) ∣ ((r - t : Nat) : Int) := by
          rw [Int.natCast_sub hge]; exact h2
        exact Int.natCast_dvd_natCast.mp h3
      obtain ⟨k, hk⟩ := hnd
      have hd := onesDownKGen a b c ha2 hb2 hc3 hab k r (by rw [Nat.mul_comm]; omega)
      rwa [show r - k * (a + b - c) = t from by rw [Nat.mul_comm]; omega] at hd
  exact reach_trans hreach (reach_trans hpile (gatherBig a b c ha2 hb2 t (by omega)))

/-- **The lie `2 + 10 = 7`** — a genuine leg-`≥ c` instance (`b = 10 > c = 7`),
    where the greedy max-value scatter measure fails — is nevertheless completely
    solvable above `M = 13`.  We discharge the two leg scatters by hand: `[2]`
    scatters directly (`2 < 7`), and `[10]` splits `10 → [5,5]` first (`5 < 7`). -/
theorem solvable_2_10_7 {s t : Nat} (hs : 13 ≤ s) (ht : 13 ≤ t)
    (h : (5:Int) ∣ ((t:Int) - s)) : Reach [⟨2,10,7⟩] [s] [t] := by
  have la : Reach [⟨2,10,7⟩] [2] (List.replicate 2 1) := scatterClean 2 10 7 2 (by omega) (by omega)
  have lb : Reach [⟨2,10,7⟩] [10] (List.replicate 10 1) := by
    have hsp : Reach [⟨2,10,7⟩] [10] [5, 5] :=
      reach_move [] (Local.nsplit 10 (by omega)
        (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    have sc5 : Reach [⟨2,10,7⟩] [5] (List.replicate 5 1) := scatterClean 2 10 7 5 (by omega) (by omega)
    have s2 : Reach [⟨2,10,7⟩] [5, 5] (List.replicate 5 1 ++ [5]) := by
      have := reach_frame [5] sc5; simpa using this
    have s3 : Reach [⟨2,10,7⟩] (List.replicate 5 1 ++ [5])
        (List.replicate 5 1 ++ List.replicate 5 1) := by
      have := reach_frame_left (List.replicate 5 1) sc5; simpa using this
    rw [replicate_one_add] at s3
    exact reach_trans hsp (reach_trans s2 s3)
  exact single_sufficiency_legGE 2 10 7 (by omega) (by omega) (by omega) (by omega) la lb
    s t (by show Mval [⟨2,10,7⟩] ≤ s; have : Mval [⟨2,10,7⟩] = 13 := by decide
            omega)
        (by show Mval [⟨2,10,7⟩] ≤ t; have : Mval [⟨2,10,7⟩] = 13 := by decide
            omega)
        (by have : gz [⟨2,10,7⟩] = 5 := by decide
            rw [this]; exact h)

#print axioms YaStupid.single_sufficiency_legGE
#print axioms YaStupid.solvable_2_10_7

end YaStupid


namespace YaStupid

/-! ### A non-hub construction for the looping config `2 + 2 = 2`

`2+2=2` *bridges* every `g`-gap above `H+1` (BFS-confirmed) yet has **no** all-ones
reachability: `2 = c` is locked (it can only false-split to `{2,2}`), so a `2` is
indestructible — no single ball ever reaches a pure-ones pile, and the hub's
`la`/`lb` are *false*.  We close it anyway, **without** the hub, via one recursive
helper `peel2 : [v] → [2, v-2]` (peel a `2` off any `v ≥ 3`).  The two pumps then
need no ones at all:

- **climb** `[n] → [n+2]`: peel a `2`, *false-split* it (`2 → {2,2}`, gaining `g`),
  remerge normally;
- **descend** `[n+2] → [n]`: peel two `2`s, *false-merge* them (`{2,2} → 2`, losing
  `g`), remerge normally.

`H = 4`, `M = 5`, `g = 2`.  This shows the leg-`≥ c` family is mechanizable even
where the hub provably cannot run. -/

/-- Peel a single `2` off any ball `v ≥ 3`: `[v] → [2, v-2]`.  Strong recursion:
    `v ∈ {3,4,5}` split directly; `v ≥ 6` splits, peels the smaller half, and
    remerges the rest (never the forbidden `{2,2}`, since `v/2 ≥ 3`). -/
theorem peel2 : ∀ v, 3 ≤ v → Reach [⟨2,2,2⟩] [v] [2, v - 2] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases h3 : v = 3
    · subst h3
      exact reach_move' [] (Local.nsplit 3 (by omega)
        (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _)
        (by decide) (Reach.refl _)
    · by_cases h4 : v = 4
      · subst h4
        exact reach_move [] (Local.nsplit 4 (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
      · by_cases h5 : v = 5
        · subst h5
          exact reach_move [] (Local.nsplit 5 (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        · -- v ≥ 6
          have hsp : Reach [⟨2,2,2⟩] [v] [v / 2, (v + 1) / 2] :=
            reach_move [] (Local.nsplit v (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          have hpe := ih (v / 2) (by omega) (by omega)        -- [v/2] → [2, v/2 - 2]
          have hfr : Reach [⟨2,2,2⟩] [v / 2, (v + 1) / 2] [2, v / 2 - 2, (v + 1) / 2] := by
            have := reach_frame [(v + 1) / 2] hpe; simpa using this
          have hcc : ∀ f ∈ ([⟨2,2,2⟩] : Config),
              ¬ ((f.a = v / 2 - 2 ∧ f.b = (v + 1) / 2) ∨ (f.a = (v + 1) / 2 ∧ f.b = v / 2 - 2)) := by
            simp only [List.mem_singleton, forall_eq]; omega
          have hmrg0 : Reach [⟨2,2,2⟩] [v / 2 - 2, (v + 1) / 2] [v / 2 - 2 + (v + 1) / 2] :=
            reach_move [] (Local.nmerge (v / 2 - 2) ((v + 1) / 2) hcc) (List.Perm.refl _) (Reach.refl _)
          have hmrg : Reach [⟨2,2,2⟩] [2, v / 2 - 2, (v + 1) / 2] [2, v - 2] := by
            have := reach_frame_left [2] hmrg0
            rw [show v / 2 - 2 + (v + 1) / 2 = v - 2 from by omega] at this
            simpa using this
          exact reach_trans hsp (reach_trans hfr hmrg)

/-- Merge `[2, n-2] → [n]` for `n ≥ 5` (normal: `n-2 ≥ 3`, so `{2,n-2} ≠ {2,2}`). -/
theorem merge2 (n : Nat) (hn : 5 ≤ n) : Reach [⟨2,2,2⟩] [2, n - 2] [n] := by
  have hcc : ∀ f ∈ ([⟨2,2,2⟩] : Config), ¬ ((f.a = 2 ∧ f.b = n - 2) ∨ (f.a = n - 2 ∧ f.b = 2)) := by
    simp only [List.mem_singleton, forall_eq]; omega
  have hm := reach_move [] (Local.nmerge 2 (n - 2) hcc) (List.Perm.refl _) (Reach.refl _)
  rw [show 2 + (n - 2) = n from by omega] at hm
  exact hm

/-- **Climb pump for `2+2=2`**: `[n] → [n+2]` for every `n ≥ 5`. -/
theorem climb_222 : ∀ n, 5 ≤ n → Reach [⟨2,2,2⟩] [n] [n + 2] := by
  intro n hn
  have hp := peel2 n (by omega)                                -- [n] → [2, n-2]
  have hfs : Reach [⟨2,2,2⟩] [2, n - 2] [2, 2, n - 2] := by     -- false-split the 2 (+g)
    have hm := reach_move [n - 2] (Local.fsplit ⟨2,2,2⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hm1 : Reach [⟨2,2,2⟩] [2, 2, n - 2] [2, n] := by         -- merge {2, n-2} → n
    have := reach_frame_left [2] (merge2 n hn); simpa using this
  have hm2 : Reach [⟨2,2,2⟩] [2, n] [n + 2] := by               -- merge {2, n} → n+2
    have hcc : ∀ f ∈ ([⟨2,2,2⟩] : Config), ¬ ((f.a = 2 ∧ f.b = n) ∨ (f.a = n ∧ f.b = 2)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm := reach_move [] (Local.nmerge 2 n hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show 2 + n = n + 2 from by omega] at hm
    exact hm
  exact reach_trans hp (reach_trans hfs (reach_trans hm1 hm2))

/-- **Descend pump for `2+2=2`**: `[n+2] → [n]` for every `n ≥ 5`. -/
theorem descend_222 : ∀ n, 5 ≤ n → Reach [⟨2,2,2⟩] [n + 2] [n] := by
  intro n hn
  have hp1 : Reach [⟨2,2,2⟩] [n + 2] [2, n] := by               -- peel a 2 off n+2
    have := peel2 (n + 2) (by omega)
    rw [show n + 2 - 2 = n from by omega] at this
    exact this
  have hp2 : Reach [⟨2,2,2⟩] [2, n] [2, 2, n - 2] := by         -- peel a 2 off the n
    have := reach_frame_left [2] (peel2 n (by omega)); simpa using this
  have hfm : Reach [⟨2,2,2⟩] [2, 2, n - 2] [2, n - 2] := by     -- false-merge {2,2} → 2 (−g)
    have hm := reach_move [n - 2] (Local.fmerge ⟨2,2,2⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  exact reach_trans hp1 (reach_trans hp2 (reach_trans hfm (merge2 n hn)))

/-- **Full sufficiency for the looping config `2 + 2 = 2`**, via the two pumps —
    *without* the all-ones hub (which provably cannot run here, since `2 = c` is
    locked and never reaches ones).  Every `s, t ≥ M = 5` with `2 ∣ (t−s)` are
    interreachable. -/
theorem single_sufficiency_222 :
    ∀ s t, Mval [⟨2,2,2⟩] ≤ s → Mval [⟨2,2,2⟩] ≤ t →
      gz [⟨2,2,2⟩] ∣ ((t : Int) - s) → Reach [⟨2,2,2⟩] [s] [t] := by
  have hg : gnat [⟨2,2,2⟩] = 2 := gnat_dpos 2 2 2 (by omega)
  have hM : Mval [⟨2,2,2⟩] = 5 := by
    have hH : Hnat [⟨2,2,2⟩] = 4 := Hnat_dpos 2 2 2 (by omega)
    show Hnat [⟨2,2,2⟩] + 1 = 5; rw [hH]
  have climb : ∀ n, Mval [⟨2,2,2⟩] ≤ n → Reach [⟨2,2,2⟩] [n] [n + gnat [⟨2,2,2⟩]] := by
    intro n hn; rw [hg]; exact climb_222 n (by omega)
  have descend : ∀ n, Mval [⟨2,2,2⟩] ≤ n → Reach [⟨2,2,2⟩] [n + gnat [⟨2,2,2⟩]] [n] := by
    intro n hn; rw [hg]; exact descend_222 n (by omega)
  intro s t hs ht hg'
  exact sufficiency_of_pumps climb descend hs ht hg'

/-- The degenerate lie `2 + 2 = 2` is completely solvable above `M = 5`. -/
theorem solvable_2_2_2 {s t : Nat} (hs : 5 ≤ s) (ht : 5 ≤ t)
    (h : (2:Int) ∣ ((t:Int) - s)) : Reach [⟨2,2,2⟩] [s] [t] := by
  refine single_sufficiency_222 s t ?_ ?_ ?_
  · have h5 : Mval [⟨2,2,2⟩] = 5 := by decide
    omega
  · have h5 : Mval [⟨2,2,2⟩] = 5 := by decide
    omega
  · have : gz [⟨2,2,2⟩] = 2 := by decide
    rw [this]; exact h

#print axioms YaStupid.peel2
#print axioms YaStupid.single_sufficiency_222
#print axioms YaStupid.solvable_2_2_2

end YaStupid


namespace YaStupid

/-! ### `1 + 14 = 7`: the legs *do* scatter to ones (the greedy measure just loops)

`1+14=7` was mischaracterized as a genuine trap like `2+2=2`.  It is not.  In
`2+2=2` the value `2 = c` is truly indestructible and `[n]` reaches **no** ones-pile.
In `1+14=7` the greedy "always split the max" measure loops
(`14 → [7,7]`, `7 → {1,14}`, `14 → [7,7]`, …), but the value `7` **escapes**:
`fsplit 7 → {1,14}` produces a `1`, and `{7,1} → 8` is a *normal* merge (`≠ {1,14}`),
with `8 → [4,4]` scattering cleanly.  So each leg reaches an *inflated* ones-pile
`1^(b + k·g)` (here `g = 8`): `[7] → 1^15`, `[14] → 1^22`.  What is false is only the
exact-count form `[14] → 1^14` (scattering must fire `≥ 1` false split, each adding
`g`).  Hence the hub *can* run on `1+14=7` given the natural *inexact* leg-scatter
facts; only `single_sufficiency_legGE`'s rigid `1^b` hypothesis missed it. -/

/-- Pull one `1` out of a `(k+1)`-ones pile sitting in front of an `x`, to merge it
    with `x`: `1^(k+1) ++ [x] ~ 1 :: x :: 1^k`. -/
theorem perm_pull (k x : Nat) :
    (List.replicate (k + 1) 1 ++ [x]).Perm (1 :: x :: List.replicate k 1) := by
  rw [List.replicate_succ]
  exact (List.perm_append_comm (l₁ := List.replicate k 1) (l₂ := [x])).cons 1

/-- Scatter `[8]` to ones in `1+14=7`: `8 → [4,4]`, each `4 < 7` scatters cleanly. -/
theorem sc8_1147 : Reach [⟨1,14,7⟩] [8] (List.replicate 8 1) := by
  have hsp : Reach [⟨1,14,7⟩] [8] [4, 4] :=
    reach_move [] (Local.nsplit 8 (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have sc4 : Reach [⟨1,14,7⟩] [4] (List.replicate 4 1) := scatterClean 1 14 7 4 (by omega) (by omega)
  have s2 : Reach [⟨1,14,7⟩] [4, 4] (List.replicate 4 1 ++ [4]) := by
    have := reach_frame [4] sc4; simpa using this
  have s3 : Reach [⟨1,14,7⟩] (List.replicate 4 1 ++ [4]) (List.replicate 4 1 ++ List.replicate 4 1) := by
    have := reach_frame_left (List.replicate 4 1) sc4; simpa using this
  rw [replicate_one_add] at s3
  exact reach_trans hsp (reach_trans s2 s3)

/-- **The `7`-escape**: `[7] → 1^15` in `1+14=7`.  `fsplit 7→{1,14}`, `nsplit 14→[7,7]`,
    `{1,7}→8` (normal!), scatter the `8`, merge a fresh `1` onto the surviving `7`,
    scatter the resulting `8`.  No greedy loop — the `{7,1}→8` step breaks it. -/
theorem escape7_1147 : Reach [⟨1,14,7⟩] [7] (List.replicate 15 1) := by
  have s1 : Reach [⟨1,14,7⟩] [7] [1, 14] := by
    have hm := reach_move [] (Local.fsplit ⟨1,14,7⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _); simpa using hm
  have s2 : Reach [⟨1,14,7⟩] [1, 14] [1, 7, 7] := by
    have hns : Reach [⟨1,14,7⟩] [14] [7, 7] :=
      reach_move [] (Local.nsplit 14 (by omega)
        (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    have := reach_frame_left [1] hns; simpa using this
  have hcc : ∀ f ∈ ([⟨1,14,7⟩] : Config), ¬ ((f.a = 1 ∧ f.b = 7) ∨ (f.a = 7 ∧ f.b = 1)) := by
    simp only [List.mem_singleton, forall_eq]; omega
  have s3 : Reach [⟨1,14,7⟩] [1, 7, 7] [8, 7] := by
    have hm := reach_move [7] (Local.nmerge 1 7 hcc) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s4 : Reach [⟨1,14,7⟩] [8, 7] (List.replicate 8 1 ++ [7]) := by
    have := reach_frame [7] sc8_1147; simpa using this
  have s5 : Reach [⟨1,14,7⟩] (List.replicate 8 1 ++ [7]) ([8] ++ List.replicate 7 1) := by
    have hm := reach_move (List.replicate 7 1) (Local.nmerge 1 7 hcc) (perm_pull 7 7) (Reach.refl _)
    simpa using hm
  have s6 : Reach [⟨1,14,7⟩] ([8] ++ List.replicate 7 1) (List.replicate 15 1) := by
    have := reach_frame (List.replicate 7 1) sc8_1147
    rw [replicate_one_add] at this; simpa using this
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 (reach_trans s4 (reach_trans s5 s6))))

/-- **The leg `14` scatters**: `[14] → 1^22` in `1+14=7`.  `14 → [7,7]`, escape one
    `7` to `1^15`, then merge a fresh `1` onto the other `7` and scatter that `8`.
    This is the inexact `lb` the hub needs — `1^(14 + 1·8)`, *not* `1^14`. -/
theorem scatter14_1147 : Reach [⟨1,14,7⟩] [14] (List.replicate 22 1) := by
  have t1 : Reach [⟨1,14,7⟩] [14] [7, 7] :=
    reach_move [] (Local.nsplit 14 (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have t2 : Reach [⟨1,14,7⟩] [7, 7] (List.replicate 15 1 ++ [7]) := by
    have := reach_frame [7] escape7_1147; simpa using this
  have hcc : ∀ f ∈ ([⟨1,14,7⟩] : Config), ¬ ((f.a = 1 ∧ f.b = 7) ∨ (f.a = 7 ∧ f.b = 1)) := by
    simp only [List.mem_singleton, forall_eq]; omega
  have t3 : Reach [⟨1,14,7⟩] (List.replicate 15 1 ++ [7]) ([8] ++ List.replicate 14 1) := by
    have hm := reach_move (List.replicate 14 1) (Local.nmerge 1 7 hcc) (perm_pull 14 7) (Reach.refl _)
    simpa using hm
  have t4 : Reach [⟨1,14,7⟩] ([8] ++ List.replicate 14 1) (List.replicate 22 1) := by
    have := reach_frame (List.replicate 14 1) sc8_1147
    rw [replicate_one_add] at this; simpa using this
  exact reach_trans t1 (reach_trans t2 (reach_trans t3 t4))

#print axioms YaStupid.escape7_1147
#print axioms YaStupid.scatter14_1147

end YaStupid


namespace YaStupid

/-! ### Closing the whole `a = b = c = k` diagonal (`single_sufficiency_kkk`)

Every `a=b=c=k` with `k ≥ 2` is a *genuine trap* — `k = c` is locked, only
false-splits to `{k,k}`, so a `k` is indestructible and no ball ever reaches ones —
exactly the obstruction that defeats the all-ones hub.  (`k = 1` is the degenerate
edge `1+1=1`, handled by the same construction.)  We close the entire diagonal
(`k ≥ 1`) with the `2+2=2` construction generalized: one recursive helper
**`peelk : [v] → [k, v-k]`** (peel a `k` off any `v ≥ k+1`) drives both pumps
(`H = 2k`, `M = 2k+1`, `g = k`):

- climb `[n] → [n+k]`: peel a `k`, *false-split* it (`k → {k,k}`, `+g`), remerge;
- descend `[n+k] → [n]`: peel two `k`s, *false-merge* them (`{k,k} → k`, `−g`), remerge.

The only twist over `peel2`: when `k ≥ 3` the sub-range `v ∈ [k+1, 2k-2]` cannot
expose a `k` by halving (both halves `< k`), so `peelk_lo` scatters `v` to ones (legal
there — the halving tree stays below `c = k`) and regathers `[k] ++ 1^(v-k)`. -/

/-- The low sub-range `k+1 ≤ v ≤ 2k-2` (only nonempty for `k ≥ 3`): halve, scatter the
    two sub-`k` halves to ones, regather a `[k]` and a `[v-k]`. -/
theorem peelk_lo (k : Nat) (hk : 3 ≤ k) :
    ∀ v, k + 1 ≤ v → v ≤ 2 * k - 2 → Reach [⟨k,k,k⟩] [v] [k, v - k] := by
  intro v h1 h2
  have hsp : Reach [⟨k,k,k⟩] [v] [v / 2, (v + 1) / 2] :=
    reach_move [] (Local.nsplit v (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hscat : Reach [⟨k,k,k⟩] [v / 2, (v + 1) / 2] (List.replicate v 1) := by
    have h := scatterList k k k [v / 2, (v + 1) / 2] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega⟩
      · rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩)
    rwa [show total [v / 2, (v + 1) / 2] = v from by
      simp only [total_cons, total_nil]; omega] at h
  have hg1 : Reach [⟨k,k,k⟩] (List.replicate v 1) (k :: List.replicate (v - k) 1) :=
    gatherPrefix k k k k v (by omega) (by omega) (by omega)
  have hg2 : Reach [⟨k,k,k⟩] (List.replicate (v - k) 1) [v - k] := by
    have := gatherPrefix k k k (v - k) (v - k) (by omega) (by omega) (by omega)
    simpa using this
  have hg3 : Reach [⟨k,k,k⟩] (k :: List.replicate (v - k) 1) [k, v - k] := by
    have := reach_frame_left [k] hg2; simpa using this
  exact reach_trans hsp (reach_trans hscat (reach_trans hg1 hg3))

/-- Peel a single `k` off any `v ≥ k+1`: `[v] → [k, v-k]`.  Strong recursion:
    `v ∈ [k+1, 2k-2]` via `peelk_lo`; `v ∈ {2k-1, 2k, 2k+1}` split directly to
    `{k, v-k}`; `v ≥ 2k+2` splits, peels the smaller half (`≥ k+1`), remerges. -/
theorem peelk (k : Nat) (hk : 1 ≤ k) : ∀ v, k + 1 ≤ v → Reach [⟨k,k,k⟩] [v] [k, v - k] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hlo : v ≤ 2 * k - 2
    · exact peelk_lo k (by omega) v hv hlo
    · by_cases h1 : v = 2 * k - 1
      · refine reach_move' [] (Local.nsplit v (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) ?_ (Reach.refl _)
        have e1 : v / 2 = k - 1 := by omega
        have e2 : (v + 1) / 2 = k := by omega
        rw [e1, e2, show v - k = k - 1 from by omega]
        exact List.Perm.swap (k - 1) k []
      · by_cases h2 : v = 2 * k
        · have hsp : Reach [⟨k,k,k⟩] [v] [v / 2, (v + 1) / 2] :=
            reach_move [] (Local.nsplit v (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          rw [show v / 2 = k from by omega, show (v + 1) / 2 = k from by omega] at hsp
          rw [show v - k = k from by omega]; exact hsp
        · by_cases h3 : v = 2 * k + 1
          · have hsp : Reach [⟨k,k,k⟩] [v] [v / 2, (v + 1) / 2] :=
              reach_move [] (Local.nsplit v (by omega)
                (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
            rw [show v / 2 = k from by omega, show (v + 1) / 2 = k + 1 from by omega] at hsp
            rw [show v - k = k + 1 from by omega]; exact hsp
          · -- v ≥ 2k+2
            have hsp : Reach [⟨k,k,k⟩] [v] [v / 2, (v + 1) / 2] :=
              reach_move [] (Local.nsplit v (by omega)
                (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
            have hpe := ih (v / 2) (by omega) (by omega)
            have hfr : Reach [⟨k,k,k⟩] [v / 2, (v + 1) / 2] [k, v / 2 - k, (v + 1) / 2] := by
              have := reach_frame [(v + 1) / 2] hpe; simpa using this
            have hcc : ∀ f ∈ ([⟨k,k,k⟩] : Config),
                ¬ ((f.a = v / 2 - k ∧ f.b = (v + 1) / 2) ∨ (f.a = (v + 1) / 2 ∧ f.b = v / 2 - k)) := by
              simp only [List.mem_singleton, forall_eq]; omega
            have hm0 : Reach [⟨k,k,k⟩] [v / 2 - k, (v + 1) / 2] [v / 2 - k + (v + 1) / 2] :=
              reach_move [] (Local.nmerge (v / 2 - k) ((v + 1) / 2) hcc) (List.Perm.refl _) (Reach.refl _)
            have hmg : Reach [⟨k,k,k⟩] [k, v / 2 - k, (v + 1) / 2] [k, v - k] := by
              have := reach_frame_left [k] hm0
              rw [show v / 2 - k + (v + 1) / 2 = v - k from by omega] at this
              simpa using this
            exact reach_trans hsp (reach_trans hfr hmg)

/-- **Climb pump for `a=b=c=k`**: `[n] → [n+k]` for every `n ≥ 2k+1`. -/
theorem climb_kkk (k : Nat) (hk : 1 ≤ k) : ∀ n, 2 * k + 1 ≤ n → Reach [⟨k,k,k⟩] [n] [n + k] := by
  intro n hn
  have hp := peelk k hk n (by omega)
  have hfs : Reach [⟨k,k,k⟩] [k, n - k] [k, k, n - k] := by
    have hm := reach_move [n - k] (Local.fsplit ⟨k,k,k⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hm1 : Reach [⟨k,k,k⟩] [k, k, n - k] [k, n] := by
    have hcc : ∀ f ∈ ([⟨k,k,k⟩] : Config), ¬ ((f.a = k ∧ f.b = n - k) ∨ (f.a = n - k ∧ f.b = k)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm0 : Reach [⟨k,k,k⟩] [k, n - k] [k + (n - k)] :=
      reach_move [] (Local.nmerge k (n - k) hcc) (List.Perm.refl _) (Reach.refl _)
    have := reach_frame_left [k] hm0
    rw [show k + (n - k) = n from by omega] at this
    simpa using this
  have hm2 : Reach [⟨k,k,k⟩] [k, n] [n + k] := by
    have hcc : ∀ f ∈ ([⟨k,k,k⟩] : Config), ¬ ((f.a = k ∧ f.b = n) ∨ (f.a = n ∧ f.b = k)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm0 := reach_move [] (Local.nmerge k n hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show k + n = n + k from by omega] at hm0
    exact hm0
  exact reach_trans hp (reach_trans hfs (reach_trans hm1 hm2))

/-- **Descend pump for `a=b=c=k`**: `[n+k] → [n]` for every `n ≥ 2k+1`. -/
theorem descend_kkk (k : Nat) (hk : 1 ≤ k) : ∀ n, 2 * k + 1 ≤ n → Reach [⟨k,k,k⟩] [n + k] [n] := by
  intro n hn
  have hp1 : Reach [⟨k,k,k⟩] [n + k] [k, n] := by
    have := peelk k hk (n + k) (by omega)
    rw [show n + k - k = n from by omega] at this
    exact this
  have hp2 : Reach [⟨k,k,k⟩] [k, n] [k, k, n - k] := by
    have := reach_frame_left [k] (peelk k hk n (by omega)); simpa using this
  have hfm : Reach [⟨k,k,k⟩] [k, k, n - k] [k, n - k] := by
    have hm := reach_move [n - k] (Local.fmerge ⟨k,k,k⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hm1 : Reach [⟨k,k,k⟩] [k, n - k] [n] := by
    have hcc : ∀ f ∈ ([⟨k,k,k⟩] : Config), ¬ ((f.a = k ∧ f.b = n - k) ∨ (f.a = n - k ∧ f.b = k)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm0 := reach_move [] (Local.nmerge k (n - k) hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show k + (n - k) = n from by omega] at hm0
    exact hm0
  exact reach_trans hp1 (reach_trans hp2 (reach_trans hfm hm1))

/-- **Full sufficiency for the entire diagonal `a = b = c = k` (`k ≥ 1`)**, via the
    two pumps — *without* the all-ones hub (which for `k ≥ 2` provably cannot run,
    since `k` is locked and never reaches ones).  Every `s, t ≥ M = 2k+1` with
    `k ∣ (t−s)` are interreachable.  Subsumes `single_sufficiency_222` (`k = 2`). -/
theorem single_sufficiency_kkk (k : Nat) (hk : 1 ≤ k) :
    ∀ s t, Mval [⟨k,k,k⟩] ≤ s → Mval [⟨k,k,k⟩] ≤ t →
      gz [⟨k,k,k⟩] ∣ ((t : Int) - s) → Reach [⟨k,k,k⟩] [s] [t] := by
  have hg : gnat [⟨k,k,k⟩] = k := by rw [gnat_dpos k k k (by omega)]; omega
  have hM : Mval [⟨k,k,k⟩] = 2 * k + 1 := by
    have hH : Hnat [⟨k,k,k⟩] = 2 * k := by rw [Hnat_dpos k k k (by omega)]; omega
    show Hnat [⟨k,k,k⟩] + 1 = 2 * k + 1; rw [hH]
  have climb : ∀ n, Mval [⟨k,k,k⟩] ≤ n → Reach [⟨k,k,k⟩] [n] [n + gnat [⟨k,k,k⟩]] := by
    intro n hn; rw [hg]; exact climb_kkk k hk n (by omega)
  have descend : ∀ n, Mval [⟨k,k,k⟩] ≤ n → Reach [⟨k,k,k⟩] [n + gnat [⟨k,k,k⟩]] [n] := by
    intro n hn; rw [hg]; exact descend_kkk k hk n (by omega)
  intro s t hs ht hg'
  exact sufficiency_of_pumps climb descend hs ht hg'

/-- The lie `3 + 3 = 3` is completely solvable above `M = 7`. -/
theorem solvable_3_3_3 {s t : Nat} (hs : 7 ≤ s) (ht : 7 ≤ t)
    (h : (3:Int) ∣ ((t:Int) - s)) : Reach [⟨3,3,3⟩] [s] [t] := by
  refine single_sufficiency_kkk 3 (by omega) s t ?_ ?_ ?_
  · have h7 : Mval [⟨3,3,3⟩] = 7 := by decide
    omega
  · have h7 : Mval [⟨3,3,3⟩] = 7 := by decide
    omega
  · have : gz [⟨3,3,3⟩] = 3 := by decide
    rw [this]; exact h

/-- The degenerate edge `1 + 1 = 1` is completely solvable above `M = 3`. -/
theorem solvable_1_1_1 {s t : Nat} (hs : 3 ≤ s) (ht : 3 ≤ t)
    (h : (1:Int) ∣ ((t:Int) - s)) : Reach [⟨1,1,1⟩] [s] [t] := by
  refine single_sufficiency_kkk 1 (by omega) s t ?_ ?_ ?_
  · have h3 : Mval [⟨1,1,1⟩] = 3 := by decide
    omega
  · have h3 : Mval [⟨1,1,1⟩] = 3 := by decide
    omega
  · have : gz [⟨1,1,1⟩] = 1 := by decide
    rw [this]; exact h

#print axioms YaStupid.peelk
#print axioms YaStupid.single_sufficiency_kkk
#print axioms YaStupid.solvable_3_3_3
#print axioms YaStupid.solvable_1_1_1

end YaStupid


namespace YaStupid

/-! ### Closing `1 + 14 = 7` — the inexact-leg hub (the last gap)

`1+14=7` (`a=1`, `b=14≥c=7`, `g=8`, `M=16`) is the representative of the last open
family: `a+b>c` with a leg `≥ c` whose legs scatter only *inexactly* — `[14]` reaches
`1^22`, never `1^14` (`scatter14_1147`).  The all-ones hub *does* run here, but two
things differ from `single_sufficiency_dpos_full`:

1. **building a ball from ones must dodge the `{1,14}` merge** (`a=1`): only `v=15`
   is blocked (`{1,14}→7`), handled by building `[13]+[2]` instead (`build1147`);
2. **the climb gains `2g` not `g`** (the leg `14` scatters to `1^22 = 1^(14+g)`), so
   `gainOneG1147` gains `2g` then sheds `g` via the leg-free `loseG1147` to net `+g`.

Everything else is the standard hub: scatter `[s]→1^r` (with the `7`-escape),
walk the pile by `g`, rebuild `[t]`. -/

/-- Pull one `1` from the front of a `(k+1)`-ones pile to sit before `x`. -/
theorem perm_pull1 (k x : Nat) :
    (List.replicate (k + 1) 1 ++ [x]).Perm (1 :: x :: List.replicate k 1) := by
  rw [List.replicate_succ]
  exact (List.perm_append_comm (l₁ := List.replicate k 1) (l₂ := [x])).cons 1

/-- Build any ball `[v]` from `v` ones in `1+14=7`, dodging the `{1,14}` merge.
    `v ≤ 14`: `gather`.  `v = 15`: build `[13] + [2]`, merge `{13,2}→15`.
    `v ≥ 16`: build `[v-1]` (recursively), merge `{1,v-1}→v` (safe: `v-1 ≠ 14`). -/
theorem build1147 : ∀ v, 1 ≤ v → Reach [⟨1,14,7⟩] (List.replicate v 1) [v] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases h14 : v ≤ 14
    · exact gather 1 14 7 v (by omega) (by omega)
    · by_cases h15 : v = 15
      · subst h15
        have key : List.replicate 15 (1:Nat) = List.replicate 13 1 ++ List.replicate 2 1 := by
          rw [replicate_one_add]
        have b13 : Reach [⟨1,14,7⟩] (List.replicate 13 1) [13] := gather 1 14 7 13 (by omega) (by omega)
        have b2 : Reach [⟨1,14,7⟩] (List.replicate 2 1) [2] := gather 1 14 7 2 (by omega) (by omega)
        have s1 : Reach [⟨1,14,7⟩] (List.replicate 15 1) ([13] ++ List.replicate 2 1) := by
          rw [key]; have := reach_frame (List.replicate 2 1) b13; simpa using this
        have s2 : Reach [⟨1,14,7⟩] ([13] ++ List.replicate 2 1) [13, 2] := by
          have := reach_frame_left [13] b2; simpa using this
        have s3 : Reach [⟨1,14,7⟩] [13, 2] [15] := by
          have hcc : ∀ f ∈ ([⟨1,14,7⟩] : Config), ¬ ((f.a = 13 ∧ f.b = 2) ∨ (f.a = 2 ∧ f.b = 13)) := by
            simp only [List.mem_singleton, forall_eq]; omega
          have hm := reach_move [] (Local.nmerge 13 2 hcc) (List.Perm.refl _) (Reach.refl _)
          simpa using hm
        exact reach_trans s1 (reach_trans s2 s3)
      · -- v ≥ 16
        have hrec := ih (v - 1) (by omega) (by omega)
        have key : List.replicate v (1:Nat) = List.replicate 1 1 ++ List.replicate (v - 1) 1 := by
          rw [replicate_one_add]; congr 1; omega
        have s1 : Reach [⟨1,14,7⟩] (List.replicate v 1) [1, v - 1] := by
          rw [key]; have := reach_frame_left (List.replicate 1 1) hrec; simpa using this
        have s2 : Reach [⟨1,14,7⟩] [1, v - 1] [v] := by
          have hcc : ∀ f ∈ ([⟨1,14,7⟩] : Config), ¬ ((f.a = 1 ∧ f.b = v - 1) ∨ (f.a = v - 1 ∧ f.b = 1)) := by
            simp only [List.mem_singleton, forall_eq]; omega
          have hm := reach_move [] (Local.nmerge 1 (v - 1) hcc) (List.Perm.refl _) (Reach.refl _)
          rw [show 1 + (v - 1) = v from by omega] at hm
          exact hm
        exact reach_trans s1 s2

/-- Scatter any ball to *some* ones-pile in `1+14=7` (`v=7` via the `escape7` route,
    everything else by halving / `scatterClean`).  Returns `r ≥ v`. -/
theorem scatter1147 : ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨1,14,7⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases h7 : v = 7
    · exact ⟨15, by omega, by rw [h7]; exact escape7_1147⟩
    · by_cases hlt : v < 7
      · exact ⟨v, by omega, scatterClean 1 14 7 v (by omega) hlt⟩
      · -- v ≥ 8
        obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        obtain ⟨r2, hr21, hr2r⟩ := ih ((v + 1) / 2) (by omega) (by omega)
        refine ⟨r1 + r2, by omega, ?_⟩
        have hns : Reach [⟨1,14,7⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have st1 : Reach [⟨1,14,7⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have st2 : Reach [⟨1,14,7⟩] (List.replicate r1 1 ++ [(v + 1) / 2])
            (List.replicate r1 1 ++ List.replicate r2 1) := by
          have := reach_frame_left (List.replicate r1 1) hr2r; simpa using this
        rw [replicate_one_add] at st2
        exact reach_trans hns (reach_trans st1 st2)

/-- Unlock a locked `7` with `K ≥ 1` spare ones: `7 :: 1^K → 1^(7+K)`
    (`{7,1}→8` is normal, then scatter the `8`). -/
theorem unlock7 : ∀ K, 1 ≤ K → Reach [⟨1,14,7⟩] (7 :: List.replicate K 1) (List.replicate (7 + K) 1) := by
  intro K hK
  have hrK : List.replicate K (1:Nat) = 1 :: List.replicate (K - 1) 1 := by
    cases K with
    | zero => omega
    | succ n => simp [List.replicate_succ]
  have hcc : ∀ f ∈ ([⟨1,14,7⟩] : Config), ¬ ((f.a = 7 ∧ f.b = 1) ∨ (f.a = 1 ∧ f.b = 7)) := by
    simp only [List.mem_singleton, forall_eq]; omega
  have s1 : Reach [⟨1,14,7⟩] (7 :: List.replicate K 1) (8 :: List.replicate (K - 1) 1) := by
    rw [hrK]
    have hm := reach_move (List.replicate (K - 1) 1) (Local.nmerge 7 1 hcc)
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have gu : Reach [⟨1,14,7⟩] [8] (List.replicate 8 1) := sc8_1147
  have s2 : Reach [⟨1,14,7⟩] (8 :: List.replicate (K - 1) 1)
      (List.replicate 8 1 ++ List.replicate (K - 1) 1) := by
    have := reach_frame (List.replicate (K - 1) 1) gu; simpa using this
  have ecat : List.replicate 8 (1:Nat) ++ List.replicate (K - 1) 1 = List.replicate (7 + K) 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [ecat] at s2
  exact reach_trans s1 s2

/-- Drop `g = 8` from a ones-pile: gather a `14`, false-merge `{1,14}→7`, unlock the
    `7`.  `1^K → 1^(K-8)` for `K ≥ 16`. -/
theorem loseG1147 : ∀ K, 16 ≤ K → Reach [⟨1,14,7⟩] (List.replicate K 1) (List.replicate (K - 8) 1) := by
  intro K hK
  have ga : Reach [⟨1,14,7⟩] (List.replicate K 1) (14 :: List.replicate (K - 14) 1) :=
    gatherPrefix 1 14 7 14 K (by omega) (by omega) (by omega)
  -- bring a 1 next to the 14 and false-merge {1,14}→7
  have hfm : Reach [⟨1,14,7⟩] (14 :: List.replicate (K - 14) 1) (7 :: List.replicate (K - 15) 1) := by
    have hrK : List.replicate (K - 14) (1:Nat) = 1 :: List.replicate (K - 15) 1 := by
      rw [show K - 14 = (K - 15) + 1 from by omega, List.replicate_succ]
    rw [hrK]
    -- state 14 :: 1 :: 1^(K-15); merge the {1,14} pair (perm to [1,14] ++ rest)
    have hm := reach_move' (List.replicate (K - 15) 1) (Local.fmerge ⟨1,14,7⟩ (List.mem_singleton.2 rfl))
      (by exact (List.Perm.swap 1 14 (List.replicate (K - 15) 1)))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hun : Reach [⟨1,14,7⟩] (7 :: List.replicate (K - 15) 1) (List.replicate (7 + (K - 15)) 1) :=
    unlock7 (K - 15) (by omega)
  rw [show 7 + (K - 15) = K - 8 from by omega] at hun
  exact reach_trans ga (reach_trans hfm hun)

/-- Gain `2g = 16` to a ones-pile: build a `7`, false-split `7→{1,14}`, scatter the
    `14` (`→1^22`).  `1^K → 1^(K+16)` for `K ≥ 7`. -/
theorem gainG1147 : ∀ K, 7 ≤ K → Reach [⟨1,14,7⟩] (List.replicate K 1) (List.replicate (K + 16) 1) := by
  intro K hK
  have gC : Reach [⟨1,14,7⟩] (List.replicate 7 1) [7] := gather 1 14 7 7 (by omega) (by omega)
  have hsplit : List.replicate K (1:Nat) = List.replicate 7 1 ++ List.replicate (K - 7) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨1,14,7⟩] (List.replicate K 1) (7 :: List.replicate (K - 7) 1) := by
    rw [hsplit]; have := reach_frame (List.replicate (K - 7) 1) gC; simpa using this
  have s2 : Reach [⟨1,14,7⟩] (7 :: List.replicate (K - 7) 1) (1 :: 14 :: List.replicate (K - 7) 1) := by
    have hm := reach_move (List.replicate (K - 7) 1)
      (Local.fsplit ⟨1,14,7⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨1,14,7⟩] (1 :: 14 :: List.replicate (K - 7) 1)
      (1 :: (List.replicate 22 1 ++ List.replicate (K - 7) 1)) := by
    have := reach_frame_left [1] (reach_frame (List.replicate (K - 7) 1) scatter14_1147)
    simpa using this
  have ecat : (1:Nat) :: (List.replicate 22 1 ++ List.replicate (K - 7) 1) = List.replicate (K + 16) 1 := by
    rw [replicate_one_add, show (1:Nat) :: List.replicate (22 + (K - 7)) 1
          = List.replicate (1 + (22 + (K - 7))) 1 from by rw [← List.replicate_succ]; congr 1; omega]
    congr 1; omega
  rw [ecat] at s3
  exact reach_trans s1 (reach_trans s2 s3)

/-- Net gain `g = 8`: gain `2g` then shed `g`.  `1^K → 1^(K+8)` for `K ≥ 16`. -/
theorem gainOneG1147 : ∀ K, 16 ≤ K → Reach [⟨1,14,7⟩] (List.replicate K 1) (List.replicate (K + 8) 1) := by
  intro K hK
  have hg := gainG1147 K (by omega)                 -- 1^K → 1^(K+16)
  have hl := loseG1147 (K + 16) (by omega)           -- 1^(K+16) → 1^(K+8)
  rw [show K + 16 - 8 = K + 8 from by omega] at hl
  exact reach_trans hg hl

/-- Walk a ones-pile UP by `8j`. -/
theorem onesUp1147 : ∀ j K, 16 ≤ K → Reach [⟨1,14,7⟩] (List.replicate K 1) (List.replicate (K + 8 * j) 1) := by
  intro j
  induction j with
  | zero => intro K hK; rw [Nat.mul_zero, Nat.add_zero]; exact Reach.refl _
  | succ j ih =>
    intro K hK
    have step := gainOneG1147 K hK
    have hrec := ih (K + 8) (by omega)
    rw [Nat.mul_succ]
    rw [show K + 8 + 8 * j = K + (8 * j + 8) from by omega] at hrec
    exact reach_trans step hrec

/-- Walk a ones-pile DOWN by `8j` (staying `≥ 16`). -/
theorem onesDown1147 : ∀ j K, 16 + 8 * j ≤ K → Reach [⟨1,14,7⟩] (List.replicate K 1) (List.replicate (K - 8 * j) 1) := by
  intro j
  induction j with
  | zero => intro K hK; rw [Nat.mul_zero, Nat.sub_zero]; exact Reach.refl _
  | succ j ih =>
    intro K hK
    have step := loseG1147 K (by omega)
    have hrec := ih (K - 8) (by omega)
    rw [Nat.mul_succ]
    rw [show K - 8 - 8 * j = K - (8 * j + 8) from by omega] at hrec
    exact reach_trans step hrec

/-- **Full sufficiency for `1 + 14 = 7`** — the representative inexact-leg `≥ c`
    config, closed through the all-ones hub.  Every `s, t ≥ M = 16` with `8 ∣ (t−s)`
    are interreachable. -/
theorem single_sufficiency_1147 :
    ∀ s t, Mval [⟨1,14,7⟩] ≤ s → Mval [⟨1,14,7⟩] ≤ t →
      gz [⟨1,14,7⟩] ∣ ((t : Int) - s) → Reach [⟨1,14,7⟩] [s] [t] := by
  have hM : Mval [⟨1,14,7⟩] = 16 := by decide
  have hgz : gz [⟨1,14,7⟩] = 8 := by decide
  intro s t hs ht hg
  rw [hM] at hs ht
  rw [hgz] at hg
  obtain ⟨r, hsr, hreach⟩ := scatter1147 s (by omega)
  have hr16 : 16 ≤ r := by omega
  -- residue: 8 ∣ (r − s)
  have hrs : (8:Int) ∣ ((r : Int) - s) := by
    have hd := reach_dvd hreach
    rw [total_replicate_one, show total [s] = s from by simp, hgz] at hd
    exact hd
  obtain ⟨p, hp⟩ := hg
  obtain ⟨q, hq⟩ := hrs
  have htr : (8:Int) ∣ ((t : Int) - r) := ⟨p - q, by rw [Int.mul_sub, ← hp, ← hq]; omega⟩
  have hpile : Reach [⟨1,14,7⟩] (List.replicate r 1) (List.replicate t 1) := by
    rcases Nat.le_total r t with hle | hge
    · have hnd : 8 ∣ (t - r) := by
        have h1 : ((8:Nat) : Int) ∣ ((t - r : Nat) : Int) := by rw [Int.natCast_sub hle]; exact htr
        exact Int.natCast_dvd_natCast.mp h1
      obtain ⟨j, hj⟩ := hnd
      have hu := onesUp1147 j r (by omega)
      rwa [show r + 8 * j = t from by omega] at hu
    · have hnd : 8 ∣ (r - t) := by
        have h2 : ((8:Nat) : Int) ∣ ((r : Int) - t) := by
          have hneg := dvd_neg' htr
          rw [show -((t:Int) - r) = (r:Int) - t from by omega] at hneg; exact hneg
        have h3 : ((8:Nat) : Int) ∣ ((r - t : Nat) : Int) := by rw [Int.natCast_sub hge]; exact h2
        exact Int.natCast_dvd_natCast.mp h3
      obtain ⟨j, hj⟩ := hnd
      have hd := onesDown1147 j r (by omega)
      rwa [show r - 8 * j = t from by omega] at hd
  have hbuild : Reach [⟨1,14,7⟩] (List.replicate t 1) [t] := build1147 t (by omega)
  exact reach_trans hreach (reach_trans hpile hbuild)

/-- The notorious lie `1 + 14 = 7` is completely solvable above `M = 16`. -/
theorem solvable_1_14_7 {s t : Nat} (hs : 16 ≤ s) (ht : 16 ≤ t)
    (h : (8:Int) ∣ ((t:Int) - s)) : Reach [⟨1,14,7⟩] [s] [t] := by
  refine single_sufficiency_1147 s t ?_ ?_ ?_
  · have : Mval [⟨1,14,7⟩] = 16 := by decide
    omega
  · have : Mval [⟨1,14,7⟩] = 16 := by decide
    omega
  · have : gz [⟨1,14,7⟩] = 8 := by decide
    rw [this]; exact h

#print axioms YaStupid.build1147
#print axioms YaStupid.scatter1147
#print axioms YaStupid.single_sufficiency_1147
#print axioms YaStupid.solvable_1_14_7

end YaStupid


namespace YaStupid

/-! ### The abstract hub: four primitives ⇒ full sufficiency

`single_sufficiency_dpos_full`, `single_sufficiency_legGE`, and
`single_sufficiency_1147` are the *same* hub argument over different leg-scatter
constructions.  Here it is once, abstractly.  For any `a+b>c`, given
  • `bld`  — build any `[v]` from `v` ones;
  • `losG` — drop `g` from a ones-pile (`1^K → 1^(K-g)`, `K ≥ M`);
  • `ganG` — gain *some* positive multiple of `g` (`1^K → 1^(K+j·g)`, `j ≥ 1`);
  • `scat` — scatter any `[v]` to *some* ones-pile,
full sufficiency follows.  The key move is `hub_gainOne`: a single `ganG` (`+j·g`)
followed by `j−1` applications of the leg-free `losG` nets exactly `+g`, so a leg
that only scatters *inexactly* (to `1^(b+k·g)`, as in `1+14=7`) is no obstacle.  Each
remaining `a+b>c`, leg-`≥ c` config reduces to discharging these four — and `scat` is
the only genuinely config-specific one (it is exactly what fails on the trap diagonal
`a=b=c`, which `peelk` handles without the hub). -/

theorem hub_onesDown (a b c : Nat)
    (losG : ∀ K, a + b + 1 ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - (a + b - c)) 1)) :
    ∀ m K, a + b + 1 + m * (a + b - c) ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - m * (a + b - c)) 1) := by
  intro m
  induction m with
  | zero => intro K hK; rw [Nat.zero_mul, Nat.sub_zero]; exact Reach.refl _
  | succ m ih =>
    intro K hK
    have hsm : (m + 1) * (a + b - c) = m * (a + b - c) + (a + b - c) := Nat.succ_mul m (a + b - c)
    have step := losG K (by omega)
    have hrec := ih (K - (a + b - c)) (by omega)
    rw [Nat.succ_mul]
    rw [show K - (a + b - c) - m * (a + b - c) = K - (m * (a + b - c) + (a + b - c)) from by omega] at hrec
    exact reach_trans step hrec

theorem hub_gainOne (a b c : Nat)
    (losG : ∀ K, a + b + 1 ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - (a + b - c)) 1))
    (ganG : ∀ K, a + b + 1 ≤ K →
      ∃ j, 1 ≤ j ∧ Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + j * (a + b - c)) 1)) :
    ∀ K, a + b + 1 ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + (a + b - c)) 1) := by
  intro K hK
  obtain ⟨j, hj1, hr⟩ := ganG K hK
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hjg : (j' + 1) * (a + b - c) = j' * (a + b - c) + (a + b - c) := Nat.succ_mul j' (a + b - c)
  have hd := hub_onesDown a b c losG j' (K + (j' + 1) * (a + b - c)) (by omega)
  rw [show K + (j' + 1) * (a + b - c) - j' * (a + b - c) = K + (a + b - c) from by omega] at hd
  exact reach_trans hr hd

theorem hub_onesUp (a b c : Nat)
    (losG : ∀ K, a + b + 1 ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - (a + b - c)) 1))
    (ganG : ∀ K, a + b + 1 ≤ K →
      ∃ j, 1 ≤ j ∧ Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + j * (a + b - c)) 1)) :
    ∀ m K, a + b + 1 ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + m * (a + b - c)) 1) := by
  intro m
  induction m with
  | zero => intro K hK; rw [Nat.zero_mul, Nat.add_zero]; exact Reach.refl _
  | succ m ih =>
    intro K hK
    have step := hub_gainOne a b c losG ganG K hK
    have hrec := ih (K + (a + b - c)) (by omega)
    rw [Nat.succ_mul]
    rw [show K + (a + b - c) + m * (a + b - c) = K + (m * (a + b - c) + (a + b - c)) from by omega] at hrec
    exact reach_trans step hrec

/-- **The abstract inexact-leg hub.**  For any `a + b > c`, the four primitives
    `bld`, `losG`, `ganG`, `scat` give full sufficiency: every `s, t ≥ M` with
    `g ∣ (t−s)` are interreachable.  (`ganG` may gain any positive multiple of `g`,
    so inexactly-scattering legs are fine — `hub_gainOne` sheds the surplus.) -/
theorem sufficiency_from_hub (a b c : Nat) (hab : c < a + b)
    (bld : ∀ v, 1 ≤ v → Reach [⟨a,b,c⟩] (List.replicate v 1) [v])
    (losG : ∀ K, a + b + 1 ≤ K →
      Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - (a + b - c)) 1))
    (ganG : ∀ K, a + b + 1 ≤ K →
      ∃ j, 1 ≤ j ∧ Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + j * (a + b - c)) 1))
    (scat : ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨a,b,c⟩] [v] (List.replicate r 1)) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  have hMv : Mval [⟨a,b,c⟩] = a + b + 1 := by
    show Hnat [⟨a,b,c⟩] + 1 = a + b + 1; rw [Hnat_dpos a b c hab]
  have hgz : gz [⟨a,b,c⟩] = ((a + b - c : Nat) : Int) := by
    show ((gnat [⟨a,b,c⟩] : Nat) : Int) = _; rw [gnat_dpos a b c hab]
  intro s t hs ht hg
  have hs' : a + b + 1 ≤ s := by omega
  have ht' : a + b + 1 ≤ t := by omega
  obtain ⟨r, hsr, hreach⟩ := scat s (by omega)
  have hr' : a + b + 1 ≤ r := by omega
  have hrs : gz [⟨a,b,c⟩] ∣ ((r : Int) - s) := by
    have hd := reach_dvd hreach
    rwa [total_replicate_one, show total [s] = s from by simp] at hd
  obtain ⟨p, hp⟩ := hg
  obtain ⟨q, hq⟩ := hrs
  have htr : gz [⟨a,b,c⟩] ∣ ((t : Int) - r) := ⟨p - q, by rw [Int.mul_sub, ← hp, ← hq]; omega⟩
  have hpile : Reach [⟨a,b,c⟩] (List.replicate r 1) (List.replicate t 1) := by
    rcases Nat.le_total r t with hle | hge
    · have hnd : (a + b - c) ∣ (t - r) := by
        have h1 : ((a + b - c : Nat) : Int) ∣ ((t - r : Nat) : Int) := by
          rw [Int.natCast_sub hle, ← hgz]; exact htr
        exact Int.natCast_dvd_natCast.mp h1
      obtain ⟨m, hm⟩ := hnd
      have hu := hub_onesUp a b c losG ganG m r (by omega)
      rwa [show r + m * (a + b - c) = t from by rw [Nat.mul_comm]; omega] at hu
    · have hnd : (a + b - c) ∣ (r - t) := by
        have h2 : ((a + b - c : Nat) : Int) ∣ ((r : Int) - t) := by
          have hneg := dvd_neg' htr
          rw [show -((t:Int) - r) = (r:Int) - t from by omega] at hneg
          rwa [hgz] at hneg
        have h3 : ((a + b - c : Nat) : Int) ∣ ((r - t : Nat) : Int) := by
          rw [Int.natCast_sub hge]; exact h2
        exact Int.natCast_dvd_natCast.mp h3
      obtain ⟨m, hm⟩ := hnd
      have hd := hub_onesDown a b c losG m r (by rw [Nat.mul_comm]; omega)
      rwa [show r - m * (a + b - c) = t from by rw [Nat.mul_comm]; omega] at hd
  exact reach_trans hreach (reach_trans hpile (bld t (by omega)))

/-- `1 + 14 = 7` re-derived through the abstract hub, discharging the four primitives
    from the `1147` constructions (`ganG` gains `2g` via `gainG1147`, so `j = 2`).
    Confirms the abstraction is faithful. -/
theorem single_sufficiency_1147_via_hub :
    ∀ s t, Mval [⟨1,14,7⟩] ≤ s → Mval [⟨1,14,7⟩] ≤ t →
      gz [⟨1,14,7⟩] ∣ ((t : Int) - s) → Reach [⟨1,14,7⟩] [s] [t] :=
  sufficiency_from_hub 1 14 7 (by omega)
    build1147
    (fun K hK => loseG1147 K (by omega))
    (fun K hK => ⟨2, by omega, by
      have := gainG1147 K (by omega)
      rwa [show K + 2 * (1 + 14 - 7) = K + 16 from by omega] at this⟩)
    scatter1147

#print axioms YaStupid.sufficiency_from_hub
#print axioms YaStupid.single_sufficiency_1147_via_hub

end YaStupid


namespace YaStupid

/-! ### Closing the `a = 1` clean-scatter family `⟨1,b,c⟩`, `c < b ≤ 2c−2`

`legGE` already covers `a+b>c`, leg-`≥c` configs whose legs scatter *exactly* — but
only for `2 ≤ a`.  This section closes the `a = 1` version uniformly: every
`⟨1,b,c⟩` with `3 ≤ c < b ≤ 2c−2`.  The bound `b ≤ 2c−2` makes `b` halve strictly
below `c`, so it scatters cleanly (no config-specific escape), and the only new
ingredient is an `a=1` builder that dodges the false merge `{1,b}` (blocked solely at
`v = b+1`).  Everything then plugs into `sufficiency_from_hub`. -/

/-- Peel one `1` off the front of a nonempty ones-pile (clean, no nested subtraction). -/
theorem repl_pull : ∀ p, 1 ≤ p → List.replicate p (1:Nat) = 1 :: List.replicate (p - 1) 1 := by
  intro p hp
  cases p with
  | zero => omega
  | succ n => simp [List.replicate_succ]

/-- Build any `[v]` from `v` ones in `⟨1,b,c⟩`, dodging `{1,b}` (only `v=b+1` is
    blocked → built as `[b-1]+[2]`). -/
theorem buildDodge1bc (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) :
    ∀ v, 1 ≤ v → Reach [⟨1,b,c⟩] (List.replicate v 1) [v] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hvb : v ≤ b
    · exact gather 1 b c v (by omega) (by omega)
    · by_cases hv1 : v = b + 1
      · subst hv1
        have key : List.replicate (b + 1) (1:Nat) = List.replicate (b - 1) 1 ++ List.replicate 2 1 := by
          rw [replicate_one_add]; congr 1; omega
        have bb1 : Reach [⟨1,b,c⟩] (List.replicate (b - 1) 1) [b - 1] := gather 1 b c (b - 1) (by omega) (by omega)
        have b2 : Reach [⟨1,b,c⟩] (List.replicate 2 1) [2] := gather 1 b c 2 (by omega) (by omega)
        have s1 : Reach [⟨1,b,c⟩] (List.replicate (b + 1) 1) ([b - 1] ++ List.replicate 2 1) := by
          rw [key]; have := reach_frame (List.replicate 2 1) bb1; simpa using this
        have s2 : Reach [⟨1,b,c⟩] ([b - 1] ++ List.replicate 2 1) [b - 1, 2] := by
          have := reach_frame_left [b - 1] b2; simpa using this
        have s3 : Reach [⟨1,b,c⟩] [b - 1, 2] [b + 1] := by
          have hcc : ∀ f ∈ ([⟨1,b,c⟩] : Config), ¬ ((f.a = b - 1 ∧ f.b = 2) ∨ (f.a = 2 ∧ f.b = b - 1)) := by
            simp only [List.mem_singleton, forall_eq]; omega
          have hm := reach_move [] (Local.nmerge (b - 1) 2 hcc) (List.Perm.refl _) (Reach.refl _)
          rw [show (b - 1) + 2 = b + 1 from by omega] at hm
          exact hm
        exact reach_trans s1 (reach_trans s2 s3)
      · have hrec := ih (v - 1) (by omega) (by omega)
        have key : List.replicate v (1:Nat) = List.replicate 1 1 ++ List.replicate (v - 1) 1 := by
          rw [replicate_one_add]; congr 1; omega
        have s1 : Reach [⟨1,b,c⟩] (List.replicate v 1) [1, v - 1] := by
          rw [key]; have := reach_frame_left (List.replicate 1 1) hrec; simpa using this
        have s2 : Reach [⟨1,b,c⟩] [1, v - 1] [v] := by
          have hcc : ∀ f ∈ ([⟨1,b,c⟩] : Config), ¬ ((f.a = 1 ∧ f.b = v - 1) ∨ (f.a = v - 1 ∧ f.b = 1)) := by
            simp only [List.mem_singleton, forall_eq]; omega
          have hm := reach_move [] (Local.nmerge 1 (v - 1) hcc) (List.Perm.refl _) (Reach.refl _)
          rw [show 1 + (v - 1) = v from by omega] at hm
          exact hm
        exact reach_trans s1 s2

/-- Scatter the leg `b` (`≤ 2c−2`, so halves `< c`) to `1^b`, cleanly. -/
theorem scatterLeg1bc (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) (hb2c : b ≤ 2 * c - 2) :
    Reach [⟨1,b,c⟩] [b] (List.replicate b 1) := by
  have hns : Reach [⟨1,b,c⟩] [b] [b / 2, (b + 1) / 2] :=
    reach_move [] (Local.nsplit b (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have s1 : Reach [⟨1,b,c⟩] [b / 2, (b + 1) / 2] (List.replicate (b / 2) 1 ++ [(b + 1) / 2]) := by
    have := reach_frame [(b + 1) / 2] (scatterClean 1 b c (b / 2) (by omega) (by omega)); simpa using this
  have s2 : Reach [⟨1,b,c⟩] (List.replicate (b / 2) 1 ++ [(b + 1) / 2])
      (List.replicate (b / 2) 1 ++ List.replicate ((b + 1) / 2) 1) := by
    have := reach_frame_left (List.replicate (b / 2) 1) (scatterClean 1 b c ((b + 1) / 2) (by omega) (by omega))
    simpa using this
  rw [replicate_one_add, show b / 2 + (b + 1) / 2 = b from by omega] at s2
  exact reach_trans hns (reach_trans s1 s2)

/-- Scatter any `[v]` to some ones-pile in `⟨1,b,c⟩` (clean — `v=c` fsplits to
    `{1,b}` and `b` scatters; no escape needed since `b ≤ 2c−2`). -/
theorem scat1bc (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) (hb2c : b ≤ 2 * c - 2) :
    ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨1,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hvc : v = c
    · refine ⟨1 + b, by omega, ?_⟩
      rw [hvc]
      have hfs : Reach [⟨1,b,c⟩] [c] [1, b] := by
        have hm := reach_move [] (Local.fsplit ⟨1,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
        simpa using hm
      have s3 : Reach [⟨1,b,c⟩] [1, b] (1 :: List.replicate b 1) := by
        have := reach_frame_left [1] (scatterLeg1bc b c hc3 hcb hb2c); simpa using this
      have e : (1:Nat) :: List.replicate b 1 = List.replicate (1 + b) 1 := by
        rw [← List.replicate_succ]; congr 1; omega
      rw [e] at s3
      exact reach_trans hfs s3
    · by_cases hlt : v < c
      · exact ⟨v, by omega, scatterClean 1 b c v (by omega) hlt⟩
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        obtain ⟨r2, hr21, hr2r⟩ := ih ((v + 1) / 2) (by omega) (by omega)
        refine ⟨r1 + r2, by omega, ?_⟩
        have hns : Reach [⟨1,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have st1 : Reach [⟨1,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have st2 : Reach [⟨1,b,c⟩] (List.replicate r1 1 ++ [(v + 1) / 2])
            (List.replicate r1 1 ++ List.replicate r2 1) := by
          have := reach_frame_left (List.replicate r1 1) hr2r; simpa using this
        rw [replicate_one_add] at st2
        exact reach_trans hns (reach_trans st1 st2)

/-- Unlock a locked `c` with `K ≥ 1` spare ones: `c :: 1^K → 1^(c+K)`
    (`{c,1}→c+1` is normal since `c ≠ b`; then scatter `c+1 ≤ 2c-2`). -/
theorem unlock1bc (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) :
    ∀ K, 1 ≤ K → Reach [⟨1,b,c⟩] (c :: List.replicate K 1) (List.replicate (c + K) 1) := by
  intro K hK
  have hrK : List.replicate K (1:Nat) = 1 :: List.replicate (K - 1) 1 := repl_pull K hK
  have hcc : ∀ f ∈ ([⟨1,b,c⟩] : Config), ¬ ((f.a = c ∧ f.b = 1) ∨ (f.a = 1 ∧ f.b = c)) := by
    simp only [List.mem_singleton, forall_eq]; omega
  have s1 : Reach [⟨1,b,c⟩] (c :: List.replicate K 1) ((c + 1) :: List.replicate (K - 1) 1) := by
    rw [hrK]
    have hm := reach_move (List.replicate (K - 1) 1) (Local.nmerge c 1 hcc) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have gu : Reach [⟨1,b,c⟩] [c + 1] (List.replicate (c + 1) 1) := getUnits 1 b c (c + 1) (by omega) (by omega)
  have s2 : Reach [⟨1,b,c⟩] ((c + 1) :: List.replicate (K - 1) 1)
      (List.replicate (c + 1) 1 ++ List.replicate (K - 1) 1) := by
    have := reach_frame (List.replicate (K - 1) 1) gu; simpa using this
  have ecat : List.replicate (c + 1) (1:Nat) ++ List.replicate (K - 1) 1 = List.replicate (c + K) 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [ecat] at s2
  exact reach_trans s1 s2

/-- Drop `g` from a ones-pile: gather a `b`, false-merge `{1,b}→c`, unlock the `c`. -/
theorem losG1bc (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) (hb2c : b ≤ 2 * c - 2) :
    ∀ K, 1 + b + 1 ≤ K → Reach [⟨1,b,c⟩] (List.replicate K 1) (List.replicate (K - (1 + b - c)) 1) := by
  intro K hK
  have gb : Reach [⟨1,b,c⟩] (List.replicate K 1) (b :: List.replicate (K - b) 1) :=
    gatherPrefix 1 b c b K (by omega) (by omega) (by omega)
  have hrK : List.replicate (K - b) (1:Nat) = 1 :: List.replicate (K - b - 1) 1 := repl_pull (K - b) (by omega)
  have hfm : Reach [⟨1,b,c⟩] (b :: List.replicate (K - b) 1) (c :: List.replicate (K - b - 1) 1) := by
    rw [hrK]
    have hm := reach_move' (List.replicate (K - b - 1) 1) (Local.fmerge ⟨1,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.swap 1 b (List.replicate (K - b - 1) 1)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hun := unlock1bc b c hc3 hcb (K - b - 1) (by omega)
  rw [show c + (K - b - 1) = K - (1 + b - c) from by omega] at hun
  exact reach_trans gb (reach_trans hfm hun)

/-- Gain `g` to a ones-pile: build a `c`, false-split `c→{1,b}`, scatter the `b`. -/
theorem ganG1bc (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) (hb2c : b ≤ 2 * c - 2) :
    ∀ K, 1 + b + 1 ≤ K → Reach [⟨1,b,c⟩] (List.replicate K 1) (List.replicate (K + (1 + b - c)) 1) := by
  intro K hK
  have gc : Reach [⟨1,b,c⟩] (List.replicate K 1) (c :: List.replicate (K - c) 1) :=
    gatherPrefix 1 b c c K (by omega) (by omega) (by omega)
  have hfs : Reach [⟨1,b,c⟩] (c :: List.replicate (K - c) 1) (1 :: b :: List.replicate (K - c) 1) := by
    have hm := reach_move (List.replicate (K - c) 1) (Local.fsplit ⟨1,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨1,b,c⟩] (1 :: b :: List.replicate (K - c) 1)
      (1 :: (List.replicate b 1 ++ List.replicate (K - c) 1)) := by
    have := reach_frame_left [1] (reach_frame (List.replicate (K - c) 1) (scatterLeg1bc b c hc3 hcb hb2c))
    simpa using this
  have ecat : (1:Nat) :: (List.replicate b 1 ++ List.replicate (K - c) 1) = List.replicate (K + (1 + b - c)) 1 := by
    rw [replicate_one_add, show (1:Nat) :: List.replicate (b + (K - c)) 1
          = List.replicate (1 + (b + (K - c))) 1 from by rw [← List.replicate_succ]; congr 1; omega]
    congr 1; omega
  rw [ecat] at s3
  exact reach_trans gc (reach_trans hfs s3)

/-- **Full sufficiency for the `a=1` clean-scatter family `⟨1,b,c⟩`, `3 ≤ c < b ≤ 2c−2`.**
    Closes the `a=1` configs `legGE` excluded.  Every `s,t ≥ M = b+2` with
    `(1+b-c) ∣ (t−s)` are interreachable. -/
theorem single_sufficiency_1bc (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) (hb2c : b ≤ 2 * c - 2) :
    ∀ s t, Mval [⟨1,b,c⟩] ≤ s → Mval [⟨1,b,c⟩] ≤ t →
      gz [⟨1,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨1,b,c⟩] [s] [t] :=
  sufficiency_from_hub 1 b c (by omega)
    (buildDodge1bc b c hc3 hcb)
    (fun K hK => losG1bc b c hc3 hcb hb2c K (by omega))
    (fun K hK => ⟨1, by omega, by
      rw [show K + 1 * (1 + b - c) = K + (1 + b - c) from by omega]
      exact ganG1bc b c hc3 hcb hb2c K (by omega)⟩)
    (scat1bc b c hc3 hcb hb2c)

/-- The lie `1 + 12 = 7` is completely solvable above `M = 14`. -/
theorem solvable_1_12_7 {s t : Nat} (hs : 14 ≤ s) (ht : 14 ≤ t)
    (h : (6:Int) ∣ ((t:Int) - s)) : Reach [⟨1,12,7⟩] [s] [t] := by
  refine single_sufficiency_1bc 12 7 (by omega) (by omega) (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨1,12,7⟩] = 14 := by decide
    omega
  · have : Mval [⟨1,12,7⟩] = 14 := by decide
    omega
  · have : gz [⟨1,12,7⟩] = 6 := by decide
    rw [this]; exact h

#print axioms YaStupid.single_sufficiency_1bc
#print axioms YaStupid.solvable_1_12_7

end YaStupid


namespace YaStupid

/-! ### Closing the inexact-scatterer family `⟨a,b,c⟩`, `2 ≤ a < c ≤ b`

These are the leg-`≥c` scatterers `legGE` misses (it needs *exact* leg scatters).
The leg `b ≥ c` may scatter only inexactly, but the small leg `a < c` lets us
bootstrap units, and a locked `c` is cleared by *bumping it with a spare unit*
(`{c,1}→c+1`, a **normal** merge, then scatter `c+1 ≤ 2c-2`).  That bump is
total-preserving, so:
- **`scatBig`** scatters *any* `[v]` given a one-reservoir (`1^K ++ [v] → 1^(K+v)`,
  all normal moves) — works in *any* config with `c ≥ 3`, `1 ∉ {a,b}`;
- **`scat0`** scatters `[v]` from scratch, bootstrapping the first units from `a < c`;
- `bld = gatherBig`, `losG = loseGposGen`, and `ganG` gains exactly `g`
  (`scatBig` adds no surplus), so everything plugs into `sufficiency_from_hub`. -/

/-- Scatter any `[v]` to ones given a nonempty one-reservoir, using only normal
    moves (a locked `c` is bumped to `c+1` by a reservoir unit). -/
theorem scatBig (a b c : Nat) (hc3 : 3 ≤ c) (hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1))) :
    ∀ v, 1 ≤ v → ∀ K, 1 ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1 ++ [v]) (List.replicate (K + v) 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv K hK
    by_cases hvc : v < c
    · have sc := scatterClean a b c v hv hvc
      have h2 := reach_frame_left (List.replicate K 1) sc
      rw [replicate_one_add] at h2
      exact h2
    · by_cases hvc2 : v = c
      · rw [hvc2]
        have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = 1 ∧ f.b = c) ∨ (f.a = c ∧ f.b = 1)) := by
          simp only [List.mem_singleton, forall_eq]; exact hsafe
        have hp : (List.replicate K 1 ++ [c]).Perm (1 :: c :: List.replicate (K - 1) 1) := by
          rw [repl_pull K hK]
          exact (List.perm_append_comm (l₁ := List.replicate (K - 1) 1) (l₂ := [c])).cons 1
        have s1 : Reach [⟨a,b,c⟩] (List.replicate K 1 ++ [c]) ((c + 1) :: List.replicate (K - 1) 1) := by
          have hm := reach_move (List.replicate (K - 1) 1) (Local.nmerge 1 c hcc) hp (Reach.refl _)
          rw [show 1 + c = c + 1 from by omega] at hm
          simpa using hm
        have gu : Reach [⟨a,b,c⟩] [c + 1] (List.replicate (c + 1) 1) := getUnits a b c (c + 1) (by omega) (by omega)
        have s2 : Reach [⟨a,b,c⟩] ((c + 1) :: List.replicate (K - 1) 1)
            (List.replicate (c + 1) 1 ++ List.replicate (K - 1) 1) := by
          have := reach_frame (List.replicate (K - 1) 1) gu; simpa using this
        have ecat : List.replicate (c + 1) (1:Nat) ++ List.replicate (K - 1) 1 = List.replicate (K + c) 1 := by
          rw [replicate_one_add]; congr 1; omega
        rw [ecat] at s2
        exact reach_trans s1 s2
      · have hns : Reach [⟨a,b,c⟩] (List.replicate K 1 ++ [v]) (List.replicate K 1 ++ [v / 2, (v + 1) / 2]) :=
          reach_frame_left (List.replicate K 1)
            (reach_move [] (Local.nsplit v (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _))
        have e1 : List.replicate K (1:Nat) ++ [v / 2, (v + 1) / 2]
            = (List.replicate K 1 ++ [v / 2]) ++ [(v + 1) / 2] := by simp
        have r1 := ih (v / 2) (by omega) (by omega) K hK
        have hfr : Reach [⟨a,b,c⟩] ((List.replicate K 1 ++ [v / 2]) ++ [(v + 1) / 2])
            (List.replicate (K + v / 2) 1 ++ [(v + 1) / 2]) := reach_frame [(v + 1) / 2] r1
        have r2 := ih ((v + 1) / 2) (by omega) (by omega) (K + v / 2) (by omega)
        rw [show K + v / 2 + (v + 1) / 2 = K + v from by omega] at r2
        rw [e1] at hns
        exact reach_trans hns (reach_trans hfr r2)

/-- Scatter any `[v]` from scratch (`2 ≤ a < c ≤ b`): bootstrap units from the small
    leg `a < c`, then `scatBig` the rest. -/
theorem scat0 (a b c : Nat) (ha2 : 2 ≤ a) (hac : a < c) (hcb : c ≤ b) (hc3 : 3 ≤ c) :
    ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨a,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hvc : v < c
    · exact ⟨v, by omega, scatterClean a b c v hv hvc⟩
    · by_cases hvc2 : v = c
      · refine ⟨a + b, by omega, ?_⟩
        rw [hvc2]
        have hfs : Reach [⟨a,b,c⟩] [c] [a, b] := by
          have hm := reach_move [] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
          simpa using hm
        have sca : Reach [⟨a,b,c⟩] [a, b] (List.replicate a 1 ++ [b]) := by
          have := reach_frame [b] (scatterClean a b c a (by omega) hac); simpa using this
        have scbig := scatBig a b c hc3 (by omega) b (by omega) a (by omega)
        exact reach_trans hfs (reach_trans sca scbig)
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        refine ⟨r1 + (v + 1) / 2, by omega, ?_⟩
        have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have s1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have scbig := scatBig a b c hc3 (by omega) ((v + 1) / 2) (by omega) r1 (by omega)
        exact reach_trans hns (reach_trans s1 scbig)

/-- Gain exactly `g` (`scatBig` adds no surplus): build a `c`, false-split `c→{a,b}`,
    scatter both legs to ones. `1^K → 1^(K+g)` for `K ≥ a+b+1`. -/
theorem ganG_ac (a b c : Nat) (ha2 : 2 ≤ a) (hac : a < c) (hcb : c ≤ b) (hc3 : 3 ≤ c) :
    ∀ K, a + b + 1 ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + (a + b - c)) 1) := by
  intro K hK
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherBig a b c ha2 (by omega) c (by omega)
  have hsplitrep : List.replicate K (1:Nat) = List.replicate c 1 ++ List.replicate (K - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨a,b,c⟩] (List.replicate K 1) (c :: List.replicate (K - c) 1) := by
    rw [hsplitrep]; have := reach_frame (List.replicate (K - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (c :: List.replicate (K - c) 1) (a :: b :: List.replicate (K - c) 1) := by
    have hm := reach_move (List.replicate (K - c) 1) (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (K - c) 1)
      (List.replicate a 1 ++ (b :: List.replicate (K - c) 1)) := by
    have := reach_frame (b :: List.replicate (K - c) 1) (scatterClean a b c a (by omega) hac); simpa using this
  have scbig := scatBig a b c hc3 (by omega) b (by omega) a (by omega)
  have s4 : Reach [⟨a,b,c⟩] (List.replicate a 1 ++ (b :: List.replicate (K - c) 1))
      (List.replicate (a + b) 1 ++ List.replicate (K - c) 1) := by
    have := reach_frame (List.replicate (K - c) 1) scbig
    simpa using this
  have ecat : List.replicate (a + b) (1:Nat) ++ List.replicate (K - c) 1 = List.replicate (K + (a + b - c)) 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [ecat] at s4
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))

/-- **Full sufficiency for the inexact-scatterer family `⟨a,b,c⟩`, `2 ≤ a < c ≤ b`.**
    Covers leg-`≥c` configs whose big leg scatters only inexactly (e.g. `2+14=7`),
    which `legGE` could not.  Every `s,t ≥ M` with `g ∣ (t−s)` are interreachable. -/
theorem single_sufficiency_ac (a b c : Nat) (ha2 : 2 ≤ a) (hac : a < c) (hcb : c ≤ b) (hc3 : 3 ≤ c) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  sufficiency_from_hub a b c (by omega)
    (gatherBig a b c ha2 (by omega))
    (loseGposGen a b c ha2 (by omega) hc3 (by omega))
    (fun K hK => ⟨1, by omega, by
      rw [show K + 1 * (a + b - c) = K + (a + b - c) from by omega]
      exact ganG_ac a b c ha2 hac hcb hc3 K hK⟩)
    (scat0 a b c ha2 hac hcb hc3)

/-- The inexact-leg lie `2 + 14 = 7` (`b = 14 = 2c`, greedy scatter loops) is
    completely solvable above `M = 17`. -/
theorem solvable_2_14_7 {s t : Nat} (hs : 17 ≤ s) (ht : 17 ≤ t)
    (h : (9:Int) ∣ ((t:Int) - s)) : Reach [⟨2,14,7⟩] [s] [t] := by
  refine single_sufficiency_ac 2 14 7 (by omega) (by omega) (by omega) (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨2,14,7⟩] = 17 := by decide
    omega
  · have : Mval [⟨2,14,7⟩] = 17 := by decide
    omega
  · have : gz [⟨2,14,7⟩] = 9 := by decide
    rw [this]; exact h

#print axioms YaStupid.scatBig
#print axioms YaStupid.single_sufficiency_ac
#print axioms YaStupid.solvable_2_14_7

end YaStupid


namespace YaStupid

/-! ### Closing the `a = 1` leg-`≥c` family `⟨1,b,c⟩`, `3 ≤ c < b` (all `b`)

With the generalized `scatBig` (which needs only `{c,1} ≠ {a,b}`, true here since
`b > c`), the `a=1` case extends to **every** `b > c`, inexact legs included
(`1+14=7`, `1+10=5`, …) — subsuming the clean `single_sufficiency_1bc`.  Build via
`buildDodge1bc`, scatter via `scat0_a1` (bootstrapping units from the `1` leg), drop
via `losG_a1` (`unlock1bc`), gain exactly `g` via `ganG_a1`. -/

/-- Scatter any `[v]` from scratch in `⟨1,b,c⟩` (`3 ≤ c < b`): the `1` leg seeds units. -/
theorem scat0_a1 (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) :
    ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨1,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hvc : v < c
    · exact ⟨v, by omega, scatterClean 1 b c v hv hvc⟩
    · by_cases hvc2 : v = c
      · refine ⟨1 + b, by omega, ?_⟩
        rw [hvc2]
        have hfs : Reach [⟨1,b,c⟩] [c] [1, b] := by
          have hm := reach_move [] (Local.fsplit ⟨1,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
          simpa using hm
        have scbig := scatBig 1 b c hc3 (by omega) b (by omega) 1 (by omega)
        exact reach_trans hfs scbig
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        refine ⟨r1 + (v + 1) / 2, by omega, ?_⟩
        have hns : Reach [⟨1,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have s1 : Reach [⟨1,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have scbig := scatBig 1 b c hc3 (by omega) ((v + 1) / 2) (by omega) r1 (by omega)
        exact reach_trans hns (reach_trans s1 scbig)

/-- Drop `g` from a ones-pile in `⟨1,b,c⟩`: gather a `b`, `fmerge {1,b}→c`, `unlock1bc`. -/
theorem losG_a1 (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) :
    ∀ K, 1 + b + 1 ≤ K → Reach [⟨1,b,c⟩] (List.replicate K 1) (List.replicate (K - (1 + b - c)) 1) := by
  intro K hK
  have gb : Reach [⟨1,b,c⟩] (List.replicate K 1) (b :: List.replicate (K - b) 1) :=
    gatherPrefix 1 b c b K (by omega) (by omega) (by omega)
  have hrK : List.replicate (K - b) (1:Nat) = 1 :: List.replicate (K - b - 1) 1 := repl_pull (K - b) (by omega)
  have hfm : Reach [⟨1,b,c⟩] (b :: List.replicate (K - b) 1) (c :: List.replicate (K - b - 1) 1) := by
    rw [hrK]
    have hm := reach_move' (List.replicate (K - b - 1) 1) (Local.fmerge ⟨1,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.swap 1 b (List.replicate (K - b - 1) 1)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hun := unlock1bc b c hc3 hcb (K - b - 1) (by omega)
  rw [show c + (K - b - 1) = K - (1 + b - c) from by omega] at hun
  exact reach_trans gb (reach_trans hfm hun)

/-- Gain exactly `g` in `⟨1,b,c⟩`: build `c` (via `gather`, `c ≤ max = b`), false-split
    `c→{1,b}`, scatter the `b` with the `1` as reservoir. -/
theorem ganG_a1 (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) :
    ∀ K, 1 + b + 1 ≤ K → Reach [⟨1,b,c⟩] (List.replicate K 1) (List.replicate (K + (1 + b - c)) 1) := by
  intro K hK
  have gC : Reach [⟨1,b,c⟩] (List.replicate c 1) [c] := gather 1 b c c (by omega) (by omega)
  have hsplitrep : List.replicate K (1:Nat) = List.replicate c 1 ++ List.replicate (K - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨1,b,c⟩] (List.replicate K 1) (c :: List.replicate (K - c) 1) := by
    rw [hsplitrep]; have := reach_frame (List.replicate (K - c) 1) gC; simpa using this
  have s2 : Reach [⟨1,b,c⟩] (c :: List.replicate (K - c) 1) (1 :: b :: List.replicate (K - c) 1) := by
    have hm := reach_move (List.replicate (K - c) 1) (Local.fsplit ⟨1,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨1,b,c⟩] (1 :: b :: List.replicate (K - c) 1)
      (List.replicate 1 1 ++ (b :: List.replicate (K - c) 1)) := by
    simpa using (Reach.refl (1 :: b :: List.replicate (K - c) 1))
  have scbig := scatBig 1 b c hc3 (by omega) b (by omega) 1 (by omega)
  have s4 : Reach [⟨1,b,c⟩] (List.replicate 1 1 ++ (b :: List.replicate (K - c) 1))
      (List.replicate (1 + b) 1 ++ List.replicate (K - c) 1) := by
    have := reach_frame (List.replicate (K - c) 1) scbig
    simpa using this
  have ecat : List.replicate (1 + b) (1:Nat) ++ List.replicate (K - c) 1 = List.replicate (K + (1 + b - c)) 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [ecat] at s4
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))

/-- **Full sufficiency for the `a=1` leg-`≥c` family `⟨1,b,c⟩`, `3 ≤ c < b`** — all `b`,
    inexact legs included.  Subsumes `single_sufficiency_1bc`. -/
theorem single_sufficiency_a1 (b c : Nat) (hc3 : 3 ≤ c) (hcb : c < b) :
    ∀ s t, Mval [⟨1,b,c⟩] ≤ s → Mval [⟨1,b,c⟩] ≤ t →
      gz [⟨1,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨1,b,c⟩] [s] [t] :=
  sufficiency_from_hub 1 b c (by omega)
    (buildDodge1bc b c hc3 hcb)
    (losG_a1 b c hc3 hcb)
    (fun K hK => ⟨1, by omega, by
      rw [show K + 1 * (1 + b - c) = K + (1 + b - c) from by omega]
      exact ganG_a1 b c hc3 hcb K hK⟩)
    (scat0_a1 b c hc3 hcb)

/-- The inexact `a=1` lie `1 + 10 = 5` (`b = 2c`) is completely solvable above `M = 12`. -/
theorem solvable_1_10_5 {s t : Nat} (hs : 12 ≤ s) (ht : 12 ≤ t)
    (h : (6:Int) ∣ ((t:Int) - s)) : Reach [⟨1,10,5⟩] [s] [t] := by
  refine single_sufficiency_a1 10 5 (by omega) (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨1,10,5⟩] = 12 := by decide
    omega
  · have : Mval [⟨1,10,5⟩] = 12 := by decide
    omega
  · have : gz [⟨1,10,5⟩] = 6 := by decide
    rw [this]; exact h

#print axioms YaStupid.single_sufficiency_a1
#print axioms YaStupid.solvable_1_10_5

end YaStupid


namespace YaStupid

/-! ### Closing `⟨a,b,c⟩` with `2 ≤ a < 2c`, `a ≠ c`, `c ≤ b` (small leg below `2c`)

Generalizes `single_sufficiency_ac` (`a < c`) to `a < 2c`: the small leg now only
needs to lie below `2c` (so it halves into a sub-`c` value plus a `≤ c` value the
reservoir bumps), giving the bootstrap unit.  `scatBig` then scatters the big leg `b`
(any `b ≥ c`).  Covers e.g. `5+5=3`, `5+8=3`. -/

/-- Scatter a leg-value `v < 2c` (`v ≠ c`) to `1^v` exactly: `v < c` clean, else halve
    (`⌊v/2⌋ < c`) and `scatBig` the `≤ c` half off that reservoir. -/
theorem scatSmall (a b c : Nat) (hc3 : 3 ≤ c) (hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1))) :
    ∀ v, 1 ≤ v → v ≠ c → v < 2 * c → Reach [⟨a,b,c⟩] [v] (List.replicate v 1) := by
  intro v hv1 hvc hv2c
  by_cases hvlt : v < c
  · exact scatterClean a b c v hv1 hvlt
  · have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
      reach_move [] (Local.nsplit v (by omega)
        (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    have s1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate (v / 2) 1 ++ [(v + 1) / 2]) := by
      have := reach_frame [(v + 1) / 2] (scatterClean a b c (v / 2) (by omega) (by omega)); simpa using this
    have scbig := scatBig a b c hc3 hsafe ((v + 1) / 2) (by omega) (v / 2) (by omega)
    have ecat : v / 2 + (v + 1) / 2 = v := by omega
    rw [ecat] at scbig
    exact reach_trans hns (reach_trans s1 scbig)

/-- Scatter any `[v]` from scratch (`2 ≤ a < 2c`, `a ≠ c`, `c ≤ b`): bootstrap units
    from the small leg `a`, then `scatBig` the rest. -/
theorem scat0g (a b c : Nat) (ha2 : 2 ≤ a) (hac : a ≠ c) (ha2c : a < 2 * c) (hcb : c ≤ b) (hc3 : 3 ≤ c) :
    ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨a,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hvc : v < c
    · exact ⟨v, by omega, scatterClean a b c v hv hvc⟩
    · by_cases hvc2 : v = c
      · refine ⟨a + b, by omega, ?_⟩
        rw [hvc2]
        have hfs : Reach [⟨a,b,c⟩] [c] [a, b] := by
          have hm := reach_move [] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
          simpa using hm
        have sca : Reach [⟨a,b,c⟩] [a, b] (List.replicate a 1 ++ [b]) := by
          have := reach_frame [b] (scatSmall a b c hc3 (by omega) a (by omega) hac ha2c); simpa using this
        have scbig := scatBig a b c hc3 (by omega) b (by omega) a (by omega)
        exact reach_trans hfs (reach_trans sca scbig)
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        refine ⟨r1 + (v + 1) / 2, by omega, ?_⟩
        have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have s1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have scbig := scatBig a b c hc3 (by omega) ((v + 1) / 2) (by omega) r1 (by omega)
        exact reach_trans hns (reach_trans s1 scbig)

/-- Gain exactly `g` (`2 ≤ a < 2c`, `a ≠ c`): build a `c`, false-split, scatter both
    legs (small via `scatSmall`, big via `scatBig`). -/
theorem ganG_g (a b c : Nat) (ha2 : 2 ≤ a) (hac : a ≠ c) (ha2c : a < 2 * c) (hcb : c ≤ b) (hc3 : 3 ≤ c) :
    ∀ K, a + b + 1 ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + (a + b - c)) 1) := by
  intro K hK
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherBig a b c ha2 (by omega) c (by omega)
  have hsplitrep : List.replicate K (1:Nat) = List.replicate c 1 ++ List.replicate (K - c) 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨a,b,c⟩] (List.replicate K 1) (c :: List.replicate (K - c) 1) := by
    rw [hsplitrep]; have := reach_frame (List.replicate (K - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (c :: List.replicate (K - c) 1) (a :: b :: List.replicate (K - c) 1) := by
    have hm := reach_move (List.replicate (K - c) 1) (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl))
      (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have s3 : Reach [⟨a,b,c⟩] (a :: b :: List.replicate (K - c) 1)
      (List.replicate a 1 ++ (b :: List.replicate (K - c) 1)) := by
    have := reach_frame (b :: List.replicate (K - c) 1) (scatSmall a b c hc3 (by omega) a (by omega) hac ha2c)
    simpa using this
  have scbig := scatBig a b c hc3 (by omega) b (by omega) a (by omega)
  have s4 : Reach [⟨a,b,c⟩] (List.replicate a 1 ++ (b :: List.replicate (K - c) 1))
      (List.replicate (a + b) 1 ++ List.replicate (K - c) 1) := by
    have := reach_frame (List.replicate (K - c) 1) scbig; simpa using this
  have ecat : List.replicate (a + b) (1:Nat) ++ List.replicate (K - c) 1 = List.replicate (K + (a + b - c)) 1 := by
    rw [replicate_one_add]; congr 1; omega
  rw [ecat] at s4
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 s4))

/-- **Full sufficiency for `⟨a,b,c⟩`, `2 ≤ a < 2c`, `a ≠ c`, `c ≤ b`, `3 ≤ c`.**
    Subsumes `single_sufficiency_ac`; covers small legs up to `2c` with any big leg. -/
theorem single_sufficiency_g (a b c : Nat) (ha2 : 2 ≤ a) (hac : a ≠ c) (ha2c : a < 2 * c) (hcb : c ≤ b) (hc3 : 3 ≤ c) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  sufficiency_from_hub a b c (by omega)
    (gatherBig a b c ha2 (by omega))
    (loseGposGen a b c ha2 (by omega) hc3 (by omega))
    (fun K hK => ⟨1, by omega, by
      rw [show K + 1 * (a + b - c) = K + (a + b - c) from by omega]
      exact ganG_g a b c ha2 hac ha2c hcb hc3 K hK⟩)
    (scat0g a b c ha2 hac ha2c hcb hc3)

/-- The lie `5 + 5 = 3` (both legs in `(c,2c)`) is completely solvable above `M = 11`. -/
theorem solvable_5_5_3 {s t : Nat} (hs : 11 ≤ s) (ht : 11 ≤ t)
    (h : (7:Int) ∣ ((t:Int) - s)) : Reach [⟨5,5,3⟩] [s] [t] := by
  refine single_sufficiency_g 5 5 3 (by omega) (by omega) (by omega) (by omega) (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨5,5,3⟩] = 11 := by decide
    omega
  · have : Mval [⟨5,5,3⟩] = 11 := by decide
    omega
  · have : gz [⟨5,5,3⟩] = 7 := by decide
    rw [this]; exact h

#print axioms YaStupid.single_sufficiency_g
#print axioms YaStupid.solvable_5_5_3

end YaStupid


namespace YaStupid

/-! ### The general inexact `legGE`: legs scatter ⇒ sufficiency (`2 ≤ a, b`)

`single_sufficiency_legGE` required *exact* leg scatters `Reach [a] (1^a)`.  But the
gain pump needs no such thing: building the `c` *at the end* of the reservoir and
`scatBig`-ing both legs left-to-right off the growing reservoir gains exactly `g`
unconditionally (`ganG_uncond`).  So only the initial scatter `scat` needs the legs,
and it needs only the **inexact** facts `∃ r, a ≤ r ∧ Reach [a] (1^r)`.  This
`single_sufficiency_legGE_inexact` subsumes `legGE`, `_ac`, and `_g` (for `2 ≤ a`):
every `2 ≤ a, b`, `c ≥ 3`, `c < a+b` config reduces to *"do the legs scatter?"*. -/

/-- Scatter any `[v]` given inexact leg scatters (`v=c` uses them; else halve). -/
theorem scatFromLegs (a b c : Nat) (hc3 : 3 ≤ c) (hab : c < a + b)
    (la : ∃ ra, a ≤ ra ∧ Reach [⟨a,b,c⟩] [a] (List.replicate ra 1))
    (lb : ∃ rb, b ≤ rb ∧ Reach [⟨a,b,c⟩] [b] (List.replicate rb 1)) :
    ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨a,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hvc : v = c
    · obtain ⟨ra, hra, Ra⟩ := la
      obtain ⟨rb, hrb, Rb⟩ := lb
      refine ⟨ra + rb, by omega, ?_⟩
      rw [hvc]
      have hfs : Reach [⟨a,b,c⟩] [c] [a, b] := by
        have hm := reach_move [] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
        simpa using hm
      have st1 : Reach [⟨a,b,c⟩] [a, b] (List.replicate ra 1 ++ [b]) := by
        have := reach_frame [b] Ra; simpa using this
      have st2 : Reach [⟨a,b,c⟩] (List.replicate ra 1 ++ [b]) (List.replicate ra 1 ++ List.replicate rb 1) := by
        have := reach_frame_left (List.replicate ra 1) Rb; simpa using this
      rw [replicate_one_add] at st2
      exact reach_trans hfs (reach_trans st1 st2)
    · by_cases hlt : v < c
      · exact ⟨v, by omega, scatterClean a b c v hv hlt⟩
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        obtain ⟨r2, hr21, hr2r⟩ := ih ((v + 1) / 2) (by omega) (by omega)
        refine ⟨r1 + r2, by omega, ?_⟩
        have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have st1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have st2 : Reach [⟨a,b,c⟩] (List.replicate r1 1 ++ [(v + 1) / 2])
            (List.replicate r1 1 ++ List.replicate r2 1) := by
          have := reach_frame_left (List.replicate r1 1) hr2r; simpa using this
        rw [replicate_one_add] at st2
        exact reach_trans hns (reach_trans st1 st2)

/-- Gain exactly `g`, **unconditionally** (`2 ≤ a, b`, `c ≥ 3`): build `c` at the
    pile's end, false-split, `scatBig` both legs left-to-right off the reservoir. -/
theorem ganG_uncond (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 3 ≤ c) (hab : c < a + b) :
    ∀ K, a + b + 1 ≤ K → Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K + (a + b - c)) 1) := by
  intro K hK
  have gC : Reach [⟨a,b,c⟩] (List.replicate c 1) [c] := gatherBig a b c ha2 hb2 c (by omega)
  have hsplit : List.replicate K (1:Nat) = List.replicate (K - c) 1 ++ List.replicate c 1 := by
    rw [replicate_one_add]; congr 1; omega
  have s1 : Reach [⟨a,b,c⟩] (List.replicate K 1) (List.replicate (K - c) 1 ++ [c]) := by
    rw [hsplit]; have := reach_frame_left (List.replicate (K - c) 1) gC; simpa using this
  have s2 : Reach [⟨a,b,c⟩] (List.replicate (K - c) 1 ++ [c]) (List.replicate (K - c) 1 ++ [a, b]) := by
    have hm := reach_frame_left (List.replicate (K - c) 1)
      (reach_move [] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _))
    simpa using hm
  -- scatBig a off reservoir 1^(K-c), framed by [b]
  have sca := scatBig a b c hc3 (by omega) a (by omega) (K - c) (by omega)
  have e2 : List.replicate (K - c) (1:Nat) ++ [a, b] = (List.replicate (K - c) 1 ++ [a]) ++ [b] := by simp
  have s3 : Reach [⟨a,b,c⟩] ((List.replicate (K - c) 1 ++ [a]) ++ [b]) (List.replicate (K - c + a) 1 ++ [b]) :=
    reach_frame [b] sca
  -- scatBig b off reservoir 1^(K-c+a)
  have scb := scatBig a b c hc3 (by omega) b (by omega) (K - c + a) (by omega)
  rw [show K - c + a + b = K + (a + b - c) from by omega] at scb
  rw [e2] at s2
  exact reach_trans s1 (reach_trans s2 (reach_trans s3 scb))

/-- **General inexact `legGE` (`2 ≤ a, b`, `c ≥ 3`, `c < a+b`).** Full sufficiency
    given only that each leg scatters to *some* ones-pile.  Subsumes `legGE` (exact
    legs), `single_sufficiency_ac`, `single_sufficiency_g` (for `2 ≤ a`). -/
theorem single_sufficiency_legGE_inexact (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc3 : 3 ≤ c) (hab : c < a + b)
    (la : ∃ ra, a ≤ ra ∧ Reach [⟨a,b,c⟩] [a] (List.replicate ra 1))
    (lb : ∃ rb, b ≤ rb ∧ Reach [⟨a,b,c⟩] [b] (List.replicate rb 1)) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  sufficiency_from_hub a b c hab
    (gatherBig a b c ha2 hb2)
    (loseGposGen a b c ha2 hb2 hc3 hab)
    (fun K hK => ⟨1, by omega, by
      rw [show K + 1 * (a + b - c) = K + (a + b - c) from by omega]
      exact ganG_uncond a b c ha2 hb2 hc3 hab K hK⟩)
    (scatFromLegs a b c hc3 hab la lb)

#print axioms YaStupid.scatFromLegs
#print axioms YaStupid.ganG_uncond
#print axioms YaStupid.single_sufficiency_legGE_inexact

end YaStupid


namespace YaStupid

/-! ### Closing the next band: both legs in `[2c+1, 4c-2]` (e.g. `7+7=3`)

A leg `ℓ ∈ [2c+1, 4c-2]` halves into `⌊ℓ/2⌋ ∈ [c, 2c-1]` and `⌈ℓ/2⌉ ∈ (c, 2c)`: the
latter self-scatters (`scatSmall`) to seed a reservoir, off which the former scatters
(`scatBigR`, the value-first reservoir scatterer).  So such legs scatter to `1^ℓ`
exactly, discharging `single_sufficiency_legGE_inexact`.  (This band contains no
`c·2^k`, so no trap values.) -/

/-- Value-first reservoir scatter: `[v] ++ 1^K → 1^(v+K)` (mirror of `scatBig`). -/
theorem scatBigR (a b c : Nat) (hc3 : 3 ≤ c) (hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1))) :
    ∀ v, 1 ≤ v → ∀ K, 1 ≤ K → Reach [⟨a,b,c⟩] ([v] ++ List.replicate K 1) (List.replicate (v + K) 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv K hK
    by_cases hvc : v < c
    · have sc := scatterClean a b c v hv hvc
      have h2 := reach_frame (List.replicate K 1) sc
      rw [replicate_one_add] at h2
      exact h2
    · by_cases hvc2 : v = c
      · rw [hvc2]
        have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = c ∧ f.b = 1) ∨ (f.a = 1 ∧ f.b = c)) := by
          simp only [List.mem_singleton, forall_eq]; intro h; exact hsafe h.symm
        have hrK : List.replicate K (1:Nat) = 1 :: List.replicate (K - 1) 1 := repl_pull K hK
        have s1 : Reach [⟨a,b,c⟩] ([c] ++ List.replicate K 1) ((c + 1) :: List.replicate (K - 1) 1) := by
          rw [hrK]
          have hm := reach_move (List.replicate (K - 1) 1) (Local.nmerge c 1 hcc) (List.Perm.refl _) (Reach.refl _)
          rw [show c + 1 = c + 1 from rfl] at hm
          simpa using hm
        have gu : Reach [⟨a,b,c⟩] [c + 1] (List.replicate (c + 1) 1) := getUnits a b c (c + 1) (by omega) (by omega)
        have s2 : Reach [⟨a,b,c⟩] ((c + 1) :: List.replicate (K - 1) 1)
            (List.replicate (c + 1) 1 ++ List.replicate (K - 1) 1) := by
          have := reach_frame (List.replicate (K - 1) 1) gu; simpa using this
        have ecat : List.replicate (c + 1) (1:Nat) ++ List.replicate (K - 1) 1 = List.replicate (c + K) 1 := by
          rw [replicate_one_add]; congr 1; omega
        rw [ecat] at s2
        exact reach_trans s1 s2
      · have hns : Reach [⟨a,b,c⟩] ([v] ++ List.replicate K 1) ([v / 2, (v + 1) / 2] ++ List.replicate K 1) :=
          reach_frame (List.replicate K 1)
            (reach_move [] (Local.nsplit v (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _))
        have r2 := ih ((v + 1) / 2) (by omega) (by omega) K hK
        have hfr : Reach [⟨a,b,c⟩] (v / 2 :: ([(v + 1) / 2] ++ List.replicate K 1))
            (v / 2 :: List.replicate ((v + 1) / 2 + K) 1) := reach_frame_left [v / 2] r2
        have r1 := ih (v / 2) (by omega) (by omega) ((v + 1) / 2 + K) (by omega)
        rw [show v / 2 + ((v + 1) / 2 + K) = v + K from by omega] at r1
        have e1 : [v / 2, (v + 1) / 2] ++ List.replicate K 1 = v / 2 :: ([(v + 1) / 2] ++ List.replicate K 1) := by simp
        rw [e1] at hns
        have e2 : (v / 2 :: List.replicate ((v + 1) / 2 + K) 1) = [v / 2] ++ List.replicate ((v + 1) / 2 + K) 1 := by simp
        rw [e2] at hfr
        exact reach_trans hns (reach_trans hfr r1)

/-- Scatter a leg `v ∈ [2c+1, 4c-2]` to `1^v` exactly. -/
theorem scatLeg2band (a b c : Nat) (hc3 : 3 ≤ c) (hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1)))
    (v : Nat) (hv1 : 2 * c + 1 ≤ v) (hv2 : v ≤ 4 * c - 2) : Reach [⟨a,b,c⟩] [v] (List.replicate v 1) := by
  have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
    reach_move [] (Local.nsplit v (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have ss := scatSmall a b c hc3 hsafe ((v + 1) / 2) (by omega) (by omega) (by omega)
  have s1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (v / 2 :: List.replicate ((v + 1) / 2) 1) := by
    have := reach_frame_left [v / 2] ss; simpa using this
  have sbr := scatBigR a b c hc3 hsafe (v / 2) (by omega) ((v + 1) / 2) (by omega)
  rw [show v / 2 + (v + 1) / 2 = v from by omega] at sbr
  have e : v / 2 :: List.replicate ((v + 1) / 2) 1 = [v / 2] ++ List.replicate ((v + 1) / 2) 1 := by simp
  rw [e] at s1
  exact reach_trans hns (reach_trans s1 sbr)

/-- **Full sufficiency for `⟨a,b,c⟩` with both legs in `[2c+1, 4c-2]`, `c ≥ 3`.**
    Covers leg-`≥2c` scatterers such as `7+7=3`. -/
theorem single_sufficiency_band (a b c : Nat) (hc3 : 3 ≤ c)
    (ha1 : 2 * c + 1 ≤ a) (ha2 : a ≤ 4 * c - 2) (hb1 : 2 * c + 1 ≤ b) (hb2 : b ≤ 4 * c - 2) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  have hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1)) := by omega
  exact single_sufficiency_legGE_inexact a b c (by omega) (by omega) hc3 (by omega)
    ⟨a, by omega, scatLeg2band a b c hc3 hsafe a ha1 ha2⟩
    ⟨b, by omega, scatLeg2band a b c hc3 hsafe b hb1 hb2⟩

/-- The leg-`≥2c` lie `7 + 7 = 3` (both legs `= 2c+1`) is completely solvable above
    `M = 15`. -/
theorem solvable_7_7_3 {s t : Nat} (hs : 15 ≤ s) (ht : 15 ≤ t)
    (h : (11:Int) ∣ ((t:Int) - s)) : Reach [⟨7,7,3⟩] [s] [t] := by
  refine single_sufficiency_band 7 7 3 (by omega) (by omega) (by omega) (by omega) (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨7,7,3⟩] = 15 := by decide
    omega
  · have : Mval [⟨7,7,3⟩] = 15 := by decide
    omega
  · have : gz [⟨7,7,3⟩] = 11 := by decide
    rw [this]; exact h

#print axioms YaStupid.scatBigR
#print axioms YaStupid.single_sufficiency_band
#print axioms YaStupid.solvable_7_7_3

end YaStupid


namespace YaStupid

/-! ### All higher bands at once: the `Scat` predicate

`Scat c v` says "`v` reaches a `(c,2c)` value by repeated halving (taking either
floor or ceil at each step)".  It holds for **every** `v` except the halving fixed
points `c·2^k`.  By induction on a `Scat` derivation, any such `v` scatters to `1^v`
(`scatStandaloneScat`): a `(c,2c)` value self-scatters (`scatSmall`); a larger value
recurses on the good half and `scatBig`s the other.  Discharging `Scat c a`, `Scat c b`
then closes **every** `2 ≤ a,b`, `c ≥ 3` config whose legs are not `c·2^k` — all
higher bands, in one theorem. -/

/-- `v` halves down (floor or ceil) into the bootstrap window `(c, 2c)`. -/
inductive Scat (c : Nat) : Nat → Prop
  | mid {v : Nat} : c < v → v < 2 * c → Scat c v
  | bigF {v : Nat} : 2 * c ≤ v → Scat c (v / 2) → Scat c v
  | bigC {v : Nat} : 2 * c ≤ v → Scat c ((v + 1) / 2) → Scat c v

/-- Any `Scat c v` value scatters to `1^v` exactly. -/
theorem scatStandaloneScat (a b c : Nat) (hc3 : 3 ≤ c)
    (hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1))) :
    ∀ {v : Nat}, Scat c v → Reach [⟨a,b,c⟩] [v] (List.replicate v 1) := by
  intro v hscat
  induction hscat with
  | mid h1 h2 => exact scatSmall a b c hc3 hsafe _ (by omega) (by omega) (by omega)
  | @bigF v hv _ ih =>
    have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
      reach_move [] (Local.nsplit v (by omega)
        (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    have s1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate (v / 2) 1 ++ [(v + 1) / 2]) := by
      have := reach_frame [(v + 1) / 2] ih; simpa using this
    have sb := scatBig a b c hc3 hsafe ((v + 1) / 2) (by omega) (v / 2) (by omega)
    rw [show v / 2 + (v + 1) / 2 = v from by omega] at sb
    exact reach_trans hns (reach_trans s1 sb)
  | @bigC v hv _ ih =>
    have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
      reach_move [] (Local.nsplit v (by omega)
        (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    have s1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (v / 2 :: List.replicate ((v + 1) / 2) 1) := by
      have := reach_frame_left [v / 2] ih; simpa using this
    have e : v / 2 :: List.replicate ((v + 1) / 2) 1 = [v / 2] ++ List.replicate ((v + 1) / 2) 1 := by simp
    rw [e] at s1
    have sb := scatBigR a b c hc3 hsafe (v / 2) (by omega) ((v + 1) / 2) (by omega)
    rw [show v / 2 + (v + 1) / 2 = v from by omega] at sb
    exact reach_trans hns (reach_trans s1 sb)

/-- **Full sufficiency for `2 ≤ a, b`, `c ≥ 3`, `c < a+b` whenever both legs are
    `Scat` (i.e. not `c·2^k`).**  Closes all higher bands uniformly. -/
theorem single_sufficiency_scat (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc3 : 3 ≤ c) (hab : c < a + b) (hsa : Scat c a) (hsb : Scat c b) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  have hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1)) := by omega
  exact single_sufficiency_legGE_inexact a b c ha2 hb2 hc3 hab
    ⟨a, Nat.le_refl a, scatStandaloneScat a b c hc3 hsafe hsa⟩
    ⟨b, Nat.le_refl b, scatStandaloneScat a b c hc3 hsafe hsb⟩

/-- The leg-`≥4c-1` lie `15 + 15 = 4` (`15 = 4c-1`, beyond every earlier band, not
    `c·2^k`) is completely solvable above `M = 31`. -/
theorem solvable_15_15_4 {s t : Nat} (hs : 31 ≤ s) (ht : 31 ≤ t)
    (h : (26:Int) ∣ ((t:Int) - s)) : Reach [⟨15,15,4⟩] [s] [t] := by
  have hsc : Scat 4 15 := Scat.bigF (by omega) (Scat.mid (by omega) (by omega))
  refine single_sufficiency_scat 15 15 4 (by omega) (by omega) (by omega) (by omega) hsc hsc s t ?_ ?_ ?_
  · have : Mval [⟨15,15,4⟩] = 31 := by decide
    omega
  · have : Mval [⟨15,15,4⟩] = 31 := by decide
    omega
  · have : gz [⟨15,15,4⟩] = 26 := by decide
    rw [this]; exact h

#print axioms YaStupid.scatStandaloneScat
#print axioms YaStupid.single_sufficiency_scat
#print axioms YaStupid.solvable_15_15_4

end YaStupid


namespace YaStupid

/-! ### One `Scat` leg suffices: `scatAll`

If `c` itself scatters to ones (`hc_scat`), then *every* `[v]` does (`scatAll`:
`v=c` uses `hc_scat`, else halve and recurse).  And `c` scatters as soon as **one**
leg is `Scat`: `fsplit c→{a,b}`, scatter that leg (`scatStandaloneScat`), `scatBig`
the other.  So **one `Scat` leg closes the config** — even if the *other* leg is
`c·2^k`.  Only configs with *both* legs `c·2^k` (genuine traps) and `c = 2` remain. -/

/-- Given `c` scatters, every `[v]` scatters (the locked `c` is the only obstruction). -/
theorem scatAll (a b c : Nat) (hc3 : 3 ≤ c) (hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1)))
    (hc_scat : ∃ rc, c ≤ rc ∧ Reach [⟨a,b,c⟩] [c] (List.replicate rc 1)) :
    ∀ v, 1 ≤ v → ∃ r, v ≤ r ∧ Reach [⟨a,b,c⟩] [v] (List.replicate r 1) := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hvc : v = c
    · rw [hvc]; exact hc_scat
    · by_cases hlt : v < c
      · exact ⟨v, by omega, scatterClean a b c v hv hlt⟩
      · obtain ⟨r1, hr11, hr1r⟩ := ih (v / 2) (by omega) (by omega)
        obtain ⟨r2, hr21, hr2r⟩ := ih ((v + 1) / 2) (by omega) (by omega)
        refine ⟨r1 + r2, by omega, ?_⟩
        have hns : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
          reach_move [] (Local.nsplit v (by omega)
            (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        have st1 : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate r1 1 ++ [(v + 1) / 2]) := by
          have := reach_frame [(v + 1) / 2] hr1r; simpa using this
        have st2 : Reach [⟨a,b,c⟩] (List.replicate r1 1 ++ [(v + 1) / 2])
            (List.replicate r1 1 ++ List.replicate r2 1) := by
          have := reach_frame_left (List.replicate r1 1) hr2r; simpa using this
        rw [replicate_one_add] at st2
        exact reach_trans hns (reach_trans st1 st2)

/-- **Full sufficiency whenever *one* leg is `Scat`** (`2 ≤ a, b`, `c ≥ 3`, `c < a+b`).
    The `Scat` leg scatters `c`; `scatAll` then scatters the other leg too (even if it
    is `c·2^k`).  Subsumes `single_sufficiency_scat`. -/
theorem single_sufficiency_oneScat (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc3 : 3 ≤ c) (hab : c < a + b) (hs : Scat c a ∨ Scat c b) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  have hsafe : ¬ ((a = 1 ∧ b = c) ∨ (a = c ∧ b = 1)) := by omega
  have hfs : Reach [⟨a,b,c⟩] [c] [a, b] := by
    have hm := reach_move [] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hc_scat : ∃ rc, c ≤ rc ∧ Reach [⟨a,b,c⟩] [c] (List.replicate rc 1) := by
    refine ⟨a + b, by omega, ?_⟩
    rcases hs with hsa | hsb
    · have sa := scatStandaloneScat a b c hc3 hsafe hsa
      have s1 : Reach [⟨a,b,c⟩] [a, b] (List.replicate a 1 ++ [b]) := by
        have := reach_frame [b] sa; simpa using this
      have sb := scatBig a b c hc3 hsafe b (by omega) a (by omega)
      exact reach_trans hfs (reach_trans s1 sb)
    · have sb := scatStandaloneScat a b c hc3 hsafe hsb
      have s1 : Reach [⟨a,b,c⟩] [a, b] (a :: List.replicate b 1) := by
        have := reach_frame_left [a] sb; simpa using this
      have e : a :: List.replicate b 1 = [a] ++ List.replicate b 1 := by simp
      rw [e] at s1
      have sbr := scatBigR a b c hc3 hsafe a (by omega) b (by omega)
      exact reach_trans hfs (reach_trans s1 sbr)
  exact single_sufficiency_legGE_inexact a b c ha2 hb2 hc3 hab
    (scatAll a b c hc3 hsafe hc_scat a (by omega))
    (scatAll a b c hc3 hsafe hc_scat b (by omega))

/-- The lie `8 + 9 = 4` — leg `8 = 2c` is `c·2^k` (not `Scat`), but leg `9` is — is
    completely solvable above `M = 18`. -/
theorem solvable_8_9_4 {s t : Nat} (hs : 18 ≤ s) (ht : 18 ≤ t)
    (h : (13:Int) ∣ ((t:Int) - s)) : Reach [⟨8,9,4⟩] [s] [t] := by
  have hsb : Scat 4 9 := Scat.bigC (by omega) (Scat.mid (by omega) (by omega))
  refine single_sufficiency_oneScat 8 9 4 (by omega) (by omega) (by omega) (by omega) (Or.inr hsb) s t ?_ ?_ ?_
  · have : Mval [⟨8,9,4⟩] = 18 := by decide
    omega
  · have : Mval [⟨8,9,4⟩] = 18 := by decide
    omega
  · have : gz [⟨8,9,4⟩] = 13 := by decide
    rw [this]; exact h

#print axioms YaStupid.scatAll
#print axioms YaStupid.single_sufficiency_oneScat
#print axioms YaStupid.solvable_8_9_4

end YaStupid


namespace YaStupid

/-! ### Closing the `a=b` traps `⟨a,a,c⟩` with `c ∣ a` (e.g. `6+6=3`, `10+10=5`)

These are the genuine traps the hub can't touch.  The escape is to **never scatter to
ones**: peel copies of the locked `c` (`peelc`, which only ever scatters values `< c`),
then build `[a]` by *merging copies of `c`* (`gatherCval`: `{c, jc} → (j+1)c`, all
normal since `c ≠ a`).  Climb peels one `c`, false-splits `c→{a,a}`, remerges; descend
peels `2(a/c)` copies of `c`, gathers two `[a]`s, false-merges `{a,a}→c`. -/

/-- General replicate-append (any base). -/
theorem repl_add (p q x : Nat) : List.replicate p x ++ List.replicate q x = List.replicate (p + q) x := by
  induction p with
  | zero => simp
  | succ p ih => simp [List.replicate_succ, ih, Nat.succ_add]

/-- Peel a `c` off any `v ≥ c+1` in `⟨a,a,c⟩` (`c < a`): low range scatters `<c` halves
    and regathers; `{2c-1,2c,2c+1}` split directly; larger recurses. -/
theorem peelc_lo (a c : Nat) (hca : c < a) (hc3 : 3 ≤ c) :
    ∀ v, c + 1 ≤ v → v ≤ 2 * c - 2 → Reach [⟨a,a,c⟩] [v] [c, v - c] := by
  intro v h1 h2
  have hsp : Reach [⟨a,a,c⟩] [v] [v / 2, (v + 1) / 2] :=
    reach_move [] (Local.nsplit v (by omega)
      (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
  have hscat : Reach [⟨a,a,c⟩] [v / 2, (v + 1) / 2] (List.replicate v 1) := by
    have h := scatterList a a c [v / 2, (v + 1) / 2] (by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega⟩
      · rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩)
    rwa [show total [v / 2, (v + 1) / 2] = v from by simp only [total_cons, total_nil]; omega] at h
  have hg1 : Reach [⟨a,a,c⟩] (List.replicate v 1) (c :: List.replicate (v - c) 1) :=
    gatherPrefix a a c c v (by omega) (by omega) (by omega)
  have hg2 : Reach [⟨a,a,c⟩] (List.replicate (v - c) 1) [v - c] := by
    have := gatherPrefix a a c (v - c) (v - c) (by omega) (by omega) (by omega); simpa using this
  have hg3 : Reach [⟨a,a,c⟩] (c :: List.replicate (v - c) 1) [c, v - c] := by
    have := reach_frame_left [c] hg2; simpa using this
  exact reach_trans hsp (reach_trans hscat (reach_trans hg1 hg3))

/-- Peel a `c` off any `v ≥ c+1`. -/
theorem peelc (a c : Nat) (hca : c < a) (hc3 : 3 ≤ c) :
    ∀ v, c + 1 ≤ v → Reach [⟨a,a,c⟩] [v] [c, v - c] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hlo : v ≤ 2 * c - 2
    · exact peelc_lo a c hca hc3 v hv hlo
    · by_cases h1 : v = 2 * c - 1
      · refine reach_move' [] (Local.nsplit v (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) ?_ (Reach.refl _)
        rw [show v / 2 = c - 1 from by omega, show (v + 1) / 2 = c from by omega, show v - c = c - 1 from by omega]
        exact List.Perm.swap (c - 1) c []
      · by_cases h2 : v = 2 * c
        · have hsp : Reach [⟨a,a,c⟩] [v] [v / 2, (v + 1) / 2] :=
            reach_move [] (Local.nsplit v (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          rw [show v / 2 = c from by omega, show (v + 1) / 2 = c from by omega] at hsp
          rw [show v - c = c from by omega]; exact hsp
        · by_cases h3 : v = 2 * c + 1
          · have hsp : Reach [⟨a,a,c⟩] [v] [v / 2, (v + 1) / 2] :=
              reach_move [] (Local.nsplit v (by omega)
                (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
            rw [show v / 2 = c from by omega, show (v + 1) / 2 = c + 1 from by omega] at hsp
            rw [show v - c = c + 1 from by omega]; exact hsp
          · have hsp : Reach [⟨a,a,c⟩] [v] [v / 2, (v + 1) / 2] :=
              reach_move [] (Local.nsplit v (by omega)
                (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
            have hpe := ih (v / 2) (by omega) (by omega)
            have hfr : Reach [⟨a,a,c⟩] [v / 2, (v + 1) / 2] [c, v / 2 - c, (v + 1) / 2] := by
              have := reach_frame [(v + 1) / 2] hpe; simpa using this
            have hcc : ∀ f ∈ ([⟨a,a,c⟩] : Config),
                ¬ ((f.a = v / 2 - c ∧ f.b = (v + 1) / 2) ∨ (f.a = (v + 1) / 2 ∧ f.b = v / 2 - c)) := by
              simp only [List.mem_singleton, forall_eq]; omega
            have hm0 : Reach [⟨a,a,c⟩] [v / 2 - c, (v + 1) / 2] [v / 2 - c + (v + 1) / 2] :=
              reach_move [] (Local.nmerge (v / 2 - c) ((v + 1) / 2) hcc) (List.Perm.refl _) (Reach.refl _)
            have hmg : Reach [⟨a,a,c⟩] [c, v / 2 - c, (v + 1) / 2] [c, v - c] := by
              have := reach_frame_left [c] hm0
              rw [show v / 2 - c + (v + 1) / 2 = v - c from by omega] at this
              simpa using this
            exact reach_trans hsp (reach_trans hfr hmg)

/-- Peel `j` copies of `c`: `[v] → c^j ++ [v - j·c]` (for `v ≥ j·c + 1`). -/
theorem peelcMany (a c : Nat) (hca : c < a) (hc3 : 3 ≤ c) :
    ∀ j v, j * c + 1 ≤ v → Reach [⟨a,a,c⟩] [v] (List.replicate j c ++ [v - j * c]) := by
  intro j
  induction j with
  | zero => intro v hv; simpa using Reach.refl [v]
  | succ j ih =>
    intro v hv
    have hsm : (j + 1) * c = j * c + c := by rw [Nat.succ_mul]
    have hp := peelc a c hca hc3 v (by omega)
    have hrec := ih (v - c) (by omega)
    have hfr := reach_frame_left [c] hrec
    have e1 : c :: (List.replicate j c ++ [v - c - j * c]) = List.replicate (j + 1) c ++ [v - (j + 1) * c] := by
      rw [show v - c - j * c = v - (j + 1) * c from by omega, List.replicate_succ, List.cons_append]
    have e2 : [c] ++ (List.replicate j c ++ [v - c - j * c]) = c :: (List.replicate j c ++ [v - c - j * c]) := by simp
    rw [e2, e1] at hfr
    exact reach_trans hp hfr

/-- Build `[m·c]` by merging `m` copies of `c` (`{c, jc} → (j+1)c`, normal since `c ≠ a`). -/
theorem gatherCval (a c : Nat) (hca : c < a) : ∀ m, 1 ≤ m → Reach [⟨a,a,c⟩] (List.replicate m c) [m * c] := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simpa using Reach.refl [c]
    · have prev := ih hmpos
      have hcc : ∀ f ∈ ([⟨a,a,c⟩] : Config), ¬ ((f.a = c ∧ f.b = m * c) ∨ (f.a = m * c ∧ f.b = c)) := by
        simp only [List.mem_singleton, forall_eq]; omega
      have step : Reach [⟨a,a,c⟩] [c, m * c] [(m + 1) * c] := by
        have hm := reach_move [] (Local.nmerge c (m * c) hcc) (List.Perm.refl _) (Reach.refl _)
        rw [show c + m * c = (m + 1) * c from by rw [Nat.succ_mul]; omega] at hm
        exact hm
      have hfr : Reach [⟨a,a,c⟩] (c :: List.replicate m c) [c, m * c] := by
        have := reach_frame_left [c] prev; simpa using this
      rw [List.replicate_succ]
      exact reach_trans hfr step

/-- **Climb pump for the trap `⟨a,a,c⟩`** (`c < a`): `[n] → [n + (2a-c)]`, `n ≥ 2a+1`.
    Peel a `c`, false-split `c→{a,a}`, remerge. -/
theorem climb_aac (a c : Nat) (hca : c < a) (hc3 : 3 ≤ c) :
    ∀ n, 2 * a + 1 ≤ n → Reach [⟨a,a,c⟩] [n] [n + (2 * a - c)] := by
  intro n hn
  have hp := peelc a c hca hc3 n (by omega)
  have hfs : Reach [⟨a,a,c⟩] [c, n - c] [a, a, n - c] := by
    have hm := reach_move [n - c] (Local.fsplit ⟨a,a,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hm1 : Reach [⟨a,a,c⟩] [a, a, n - c] [a, a + (n - c)] := by
    have hcc : ∀ f ∈ ([⟨a,a,c⟩] : Config), ¬ ((f.a = a ∧ f.b = n - c) ∨ (f.a = n - c ∧ f.b = a)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm0 : Reach [⟨a,a,c⟩] [a, n - c] [a + (n - c)] :=
      reach_move [] (Local.nmerge a (n - c) hcc) (List.Perm.refl _) (Reach.refl _)
    have := reach_frame_left [a] hm0; simpa using this
  have hm2 : Reach [⟨a,a,c⟩] [a, a + (n - c)] [n + (2 * a - c)] := by
    have hcc : ∀ f ∈ ([⟨a,a,c⟩] : Config), ¬ ((f.a = a ∧ f.b = a + (n - c)) ∨ (f.a = a + (n - c) ∧ f.b = a)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm0 := reach_move [] (Local.nmerge a (a + (n - c)) hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show a + (a + (n - c)) = n + (2 * a - c) from by omega] at hm0
    exact hm0
  exact reach_trans hp (reach_trans hfs (reach_trans hm1 hm2))

/-- **Descend pump for the trap `⟨a,a,c⟩`** (`c < a`, `c ∣ a`): `[n+(2a-c)] → [n]`.
    Peel `2(a/c)` copies of `c`, gather two `[a]`s, false-merge `{a,a}→c`, remerge. -/
theorem descend_aac (a c : Nat) (hca : c < a) (hc3 : 3 ≤ c) (hdvd : c ∣ a) :
    ∀ n, 2 * a + 1 ≤ n → Reach [⟨a,a,c⟩] [n + (2 * a - c)] [n] := by
  intro n hn
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 1 ≤ m := by rcases m with _ | k <;> omega
  have hmc : m * c = a := by rw [Nat.mul_comm]; omega
  have h2mc : 2 * m * c = 2 * a := by rw [Nat.mul_assoc]; omega
  have ga : Reach [⟨a,a,c⟩] (List.replicate m c) [a] := by
    have := gatherCval a c hca m hm1; rwa [hmc] at this
  have hpe := peelcMany a c hca hc3 (2 * m) (n + (2 * a - c)) (by omega)
  rw [show n + (2 * a - c) - 2 * m * c = n - c from by omega] at hpe
  have e : List.replicate (2 * m) c ++ [n - c]
      = List.replicate m c ++ (List.replicate m c ++ [n - c]) := by
    rw [show 2 * m = m + m from by omega, ← repl_add, List.append_assoc]
  rw [e] at hpe
  have g1 : Reach [⟨a,a,c⟩] (List.replicate m c ++ (List.replicate m c ++ [n - c]))
      (a :: (List.replicate m c ++ [n - c])) := by
    have := reach_frame (List.replicate m c ++ [n - c]) ga; simpa using this
  have g2 : Reach [⟨a,a,c⟩] (a :: (List.replicate m c ++ [n - c])) [a, a, n - c] := by
    have := reach_frame_left [a] (reach_frame [n - c] ga); simpa using this
  have hfm : Reach [⟨a,a,c⟩] [a, a, n - c] [c, n - c] := by
    have hm := reach_move [n - c] (Local.fmerge ⟨a,a,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hmg : Reach [⟨a,a,c⟩] [c, n - c] [n] := by
    have hcc : ∀ f ∈ ([⟨a,a,c⟩] : Config), ¬ ((f.a = c ∧ f.b = n - c) ∨ (f.a = n - c ∧ f.b = c)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hmm := reach_move [] (Local.nmerge c (n - c) hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show c + (n - c) = n from by omega] at hmm
    exact hmm
  exact reach_trans hpe (reach_trans g1 (reach_trans g2 (reach_trans hfm hmg)))

/-- **Full sufficiency for the `a=b` trap `⟨a,a,c⟩` with `c ∣ a`, `c < a`, `3 ≤ c`** —
    the genuine traps (`6+6=3`, `10+10=5`, `12+12=3`, …), closed *without* the all-ones
    hub. Every `s,t ≥ M = 2a+1` with `(2a-c) ∣ (t−s)` are interreachable. -/
theorem single_sufficiency_aac (a c : Nat) (hca : c < a) (hc3 : 3 ≤ c) (hdvd : c ∣ a) :
    ∀ s t, Mval [⟨a,a,c⟩] ≤ s → Mval [⟨a,a,c⟩] ≤ t →
      gz [⟨a,a,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,a,c⟩] [s] [t] := by
  have hg : gnat [⟨a,a,c⟩] = 2 * a - c := by rw [gnat_dpos a a c (by omega)]; omega
  have hM : Mval [⟨a,a,c⟩] = 2 * a + 1 := by
    have hH : Hnat [⟨a,a,c⟩] = 2 * a := by rw [Hnat_dpos a a c (by omega)]; omega
    show Hnat [⟨a,a,c⟩] + 1 = 2 * a + 1; rw [hH]
  have climb : ∀ n, Mval [⟨a,a,c⟩] ≤ n → Reach [⟨a,a,c⟩] [n] [n + gnat [⟨a,a,c⟩]] := by
    intro n hn; rw [hg]; exact climb_aac a c hca hc3 n (by omega)
  have descend : ∀ n, Mval [⟨a,a,c⟩] ≤ n → Reach [⟨a,a,c⟩] [n + gnat [⟨a,a,c⟩]] [n] := by
    intro n hn; rw [hg]; exact descend_aac a c hca hc3 hdvd n (by omega)
  intro s t hs ht hg'
  exact sufficiency_of_pumps climb descend hs ht hg'

/-- The trap `6 + 6 = 3` (`a=b=2c`, `[M]` reaches no ones-pile) is completely solvable
    above `M = 13`. -/
theorem solvable_6_6_3 {s t : Nat} (hs : 13 ≤ s) (ht : 13 ≤ t)
    (h : (9:Int) ∣ ((t:Int) - s)) : Reach [⟨6,6,3⟩] [s] [t] := by
  refine single_sufficiency_aac 6 3 (by omega) (by omega) ⟨2, by omega⟩ s t ?_ ?_ ?_
  · have : Mval [⟨6,6,3⟩] = 13 := by decide
    omega
  · have : Mval [⟨6,6,3⟩] = 13 := by decide
    omega
  · have : gz [⟨6,6,3⟩] = 9 := by decide
    rw [this]; exact h

#print axioms YaStupid.single_sufficiency_aac
#print axioms YaStupid.solvable_6_6_3

end YaStupid


namespace YaStupid

/-! ### Generalizing the trap escape to `a ≠ b`: `peelcG`, `gatherCvalG`

The `a=b` trap closure (`single_sufficiency_aac`) used `peelc`/`gatherCval` on
`⟨a,a,c⟩`.  The genuine `c·2^k` traps with `a ≠ b` are `⟨c·2^i, c·2^j, c⟩`.  We
generalize the two primitives to `⟨a,b,c⟩` (`a < b`).  The only new obstruction is
the recursive-merge coincidence `{v/2−c, (v+1)/2} = {a,b}`, which forces
`b − a ∈ {c, c+1}`; the hypothesis `hsep : b < a + c ∨ a + c + 1 < b` rules it out
(every `c·2^k` trap with `a<b` other than `⟨c,2c,c⟩` satisfies `b − a ≥ 2c`). -/

/-- Peel a `c` off any `v ≥ c+1` in `⟨a,b,c⟩` (`2 ≤ a,b`, `c ≤ b`, separation `hsep`:
    `|a−b| ∉ {c, c+1}`, which rules out the recursive-merge coincidence). -/
theorem peelcG (a b c : Nat) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc3 : 2 ≤ c) (hcb : c ≤ b)
    (hsep : b ≠ a + c ∧ b ≠ a + c + 1 ∧ a ≠ b + c ∧ a ≠ b + c + 1) :
    ∀ v, c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] [c, v - c] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hlo : v ≤ 2 * c - 2
    · -- low range: scatter both halves (< c) to ones, regather [c, v-c]
      have hsp : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
        reach_move [] (Local.nsplit v (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
      have hscat : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] (List.replicate v 1) := by
        have h := scatterList a b c [v / 2, (v + 1) / 2] (by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨by omega, by omega⟩
          · rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩)
        rwa [show total [v / 2, (v + 1) / 2] = v from by simp only [total_cons, total_nil]; omega] at h
      have hg1 : Reach [⟨a,b,c⟩] (List.replicate v 1) (c :: List.replicate (v - c) 1) :=
        gatherPrefix a b c c v (by omega) (by omega) (by omega)
      have hg2 : Reach [⟨a,b,c⟩] (List.replicate (v - c) 1) [v - c] := by
        have := gatherPrefix a b c (v - c) (v - c) (by omega) (by omega) (by omega); simpa using this
      have hg3 : Reach [⟨a,b,c⟩] (c :: List.replicate (v - c) 1) [c, v - c] := by
        have := reach_frame_left [c] hg2; simpa using this
      exact reach_trans hsp (reach_trans hscat (reach_trans hg1 hg3))
    · by_cases h1 : v = 2 * c - 1
      · refine reach_move' [] (Local.nsplit v (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) ?_ (Reach.refl _)
        rw [show v / 2 = c - 1 from by omega, show (v + 1) / 2 = c from by omega, show v - c = c - 1 from by omega]
        exact List.Perm.swap (c - 1) c []
      · by_cases h2 : v = 2 * c
        · have hsp : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
            reach_move [] (Local.nsplit v (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          rw [show v / 2 = c from by omega, show (v + 1) / 2 = c from by omega] at hsp
          rw [show v - c = c from by omega]; exact hsp
        · by_cases h3 : v = 2 * c + 1
          · have hsp : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
              reach_move [] (Local.nsplit v (by omega)
                (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
            rw [show v / 2 = c from by omega, show (v + 1) / 2 = c + 1 from by omega] at hsp
            rw [show v - c = c + 1 from by omega]; exact hsp
          · -- recursion: v ≥ 2c+2; peel c off v/2, merge {v/2-c, (v+1)/2}
            have hsp : Reach [⟨a,b,c⟩] [v] [v / 2, (v + 1) / 2] :=
              reach_move [] (Local.nsplit v (by omega)
                (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
            have hpe := ih (v / 2) (by omega) (by omega)
            have hfr : Reach [⟨a,b,c⟩] [v / 2, (v + 1) / 2] [c, v / 2 - c, (v + 1) / 2] := by
              have := reach_frame [(v + 1) / 2] hpe; simpa using this
            have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config),
                ¬ ((f.a = v / 2 - c ∧ f.b = (v + 1) / 2) ∨ (f.a = (v + 1) / 2 ∧ f.b = v / 2 - c)) := by
              simp only [List.mem_singleton, forall_eq]; omega
            have hm0 : Reach [⟨a,b,c⟩] [v / 2 - c, (v + 1) / 2] [v / 2 - c + (v + 1) / 2] :=
              reach_move [] (Local.nmerge (v / 2 - c) ((v + 1) / 2) hcc) (List.Perm.refl _) (Reach.refl _)
            have hmg : Reach [⟨a,b,c⟩] [c, v / 2 - c, (v + 1) / 2] [c, v - c] := by
              have := reach_frame_left [c] hm0
              rw [show v / 2 - c + (v + 1) / 2 = v - c from by omega] at this
              simpa using this
            exact reach_trans hsp (reach_trans hfr hmg)

#print axioms YaStupid.peelcG

end YaStupid


namespace YaStupid

/-! ### The lone hard value: `peel4c` for `⟨c,2c,c⟩`

In `⟨c,2c,c⟩` (`a=c`, `b=2c`, so `b=a+c`) the recursive-merge coincidence
`{v/2−c,(v+1)/2} = {a,b}` actually fires, at `v = 4c` (`[4c] = [2c,2c]`, peeling a
`c` off either `2c` lands on the forbidden `{c,2c}`).  Reaching `[c,3c]` needs `3c`,
which can only come from splitting `6c`; the route dips through total `8c` (two
false splits `c→{c,2c}`) and rides two false merges `{c,2c}→c` back down.  This is
the one genuinely bespoke step; everything else recurses around it. -/

/-- `[4c] → [c, 3c]` in `⟨c,2c,c⟩` (`c ≥ 3`): the 11-move escape. -/
theorem peel4c (c : Nat) (hc3 : 3 ≤ c) :
    Reach [⟨c, 2*c, c⟩] [4*c] [c, 3*c] := by
  -- 1: split 4c → [2c,2c]
  have step1 : Reach [⟨c,2*c,c⟩] [4*c] [2*c,2*c] := by
    have h : Reach [⟨c,2*c,c⟩] [4*c] [(4*c)/2,(4*c+1)/2] :=
      reach_move [] (Local.nsplit (4*c) (by omega) (by simp only [List.mem_singleton, forall_eq]; omega))
        (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
    rwa [show (4*c)/2 = 2*c from by omega, show (4*c+1)/2 = 2*c from by omega] at h
  -- 2: split first 2c → [c,c,2c]
  have step2 : Reach [⟨c,2*c,c⟩] [2*c,2*c] [c,c,2*c] := by
    have h : Reach [⟨c,2*c,c⟩] [2*c,2*c] ([(2*c)/2,(2*c+1)/2] ++ [2*c]) :=
      reach_move [2*c] (Local.nsplit (2*c) (by omega) (by simp only [List.mem_singleton, forall_eq]; omega))
        (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
    rw [show (2*c)/2 = c from by omega, show (2*c+1)/2 = c from by omega] at h; exact h
  -- 3: fsplit first c → [c,2c,c,2c]
  have step3 : Reach [⟨c,2*c,c⟩] [c,c,2*c] [c,2*c,c,2*c] :=
    reach_move [c,2*c] (Local.fsplit ⟨c,2*c,c⟩ (List.mem_singleton.2 rfl))
      (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
  -- 4: fsplit another c → [c,2c,c,2c,2c]
  have step4 : Reach [⟨c,2*c,c⟩] [c,2*c,c,2*c] [c,2*c,c,2*c,2*c] :=
    reach_move [c,2*c,2*c] (Local.fsplit ⟨c,2*c,c⟩ (List.mem_singleton.2 rfl))
      (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
  -- 5: merge {2c,2c} → 4c : [4c,c,c,2c]
  have step5 : Reach [⟨c,2*c,c⟩] [c,2*c,c,2*c,2*c] [4*c,c,c,2*c] := by
    have h : Reach [⟨c,2*c,c⟩] [c,2*c,c,2*c,2*c] ([(2*c)+(2*c)] ++ [c,c,2*c]) :=
      reach_move [c,c,2*c] (Local.nmerge (2*c) (2*c) (by simp only [List.mem_singleton, forall_eq]; omega))
        (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
    rwa [show (2*c)+(2*c) = 4*c from by omega] at h
  -- 6: merge {2c,4c} → 6c : [6c,c,c]
  have step6 : Reach [⟨c,2*c,c⟩] [4*c,c,c,2*c] [6*c,c,c] := by
    have h : Reach [⟨c,2*c,c⟩] [4*c,c,c,2*c] ([(2*c)+(4*c)] ++ [c,c]) :=
      reach_move [c,c] (Local.nmerge (2*c) (4*c) (by simp only [List.mem_singleton, forall_eq]; omega))
        (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
    rwa [show (2*c)+(4*c) = 6*c from by omega] at h
  -- 7: split 6c → [3c,3c,c,c]
  have step7 : Reach [⟨c,2*c,c⟩] [6*c,c,c] [3*c,3*c,c,c] := by
    have h : Reach [⟨c,2*c,c⟩] [6*c,c,c] ([(6*c)/2,(6*c+1)/2] ++ [c,c]) :=
      reach_move [c,c] (Local.nsplit (6*c) (by omega) (by simp only [List.mem_singleton, forall_eq]; omega))
        (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
    rw [show (6*c)/2 = 3*c from by omega, show (6*c+1)/2 = 3*c from by omega] at h; exact h
  -- 8: merge {c,3c} → 4c : [4c,c,3c]
  have step8 : Reach [⟨c,2*c,c⟩] [3*c,3*c,c,c] [4*c,c,3*c] := by
    have h : Reach [⟨c,2*c,c⟩] [3*c,3*c,c,c] ([c+(3*c)] ++ [c,3*c]) :=
      reach_move [c,3*c] (Local.nmerge c (3*c) (by simp only [List.mem_singleton, forall_eq]; omega))
        (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
    rwa [show c+(3*c) = 4*c from by omega] at h
  -- 9: split 4c → [2c,2c,c,3c]
  have step9 : Reach [⟨c,2*c,c⟩] [4*c,c,3*c] [2*c,2*c,c,3*c] := by
    have h : Reach [⟨c,2*c,c⟩] [4*c,c,3*c] ([(4*c)/2,(4*c+1)/2] ++ [c,3*c]) :=
      reach_move [c,3*c] (Local.nsplit (4*c) (by omega) (by simp only [List.mem_singleton, forall_eq]; omega))
        (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
    rw [show (4*c)/2 = 2*c from by omega, show (4*c+1)/2 = 2*c from by omega] at h; exact h
  -- 10: fmerge {c,2c} → c : [c,2c,3c]
  have step10 : Reach [⟨c,2*c,c⟩] [2*c,2*c,c,3*c] [c,2*c,3*c] :=
    reach_move [2*c,3*c] (Local.fmerge ⟨c,2*c,c⟩ (List.mem_singleton.2 rfl))
      (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
  -- 11: fmerge {c,2c} → c : [c,3c]
  have step11 : Reach [⟨c,2*c,c⟩] [c,2*c,3*c] [c,3*c] :=
    reach_move [3*c] (Local.fmerge ⟨c,2*c,c⟩ (List.mem_singleton.2 rfl))
      (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
  exact reach_trans step1 (reach_trans step2 (reach_trans step3 (reach_trans step4
    (reach_trans step5 (reach_trans step6 (reach_trans step7 (reach_trans step8
    (reach_trans step9 (reach_trans step10 step11)))))))))

#print axioms YaStupid.peel4c

end YaStupid


namespace YaStupid

/-- **`peelc` for the pathological shape `⟨c,2c,c⟩`** (`c ≥ 3`): peel a `c` off any
    `v ≥ c+1`.  Identical recursion to `peelcG`, but the lone bad value `v = 4c`
    (where `{v/2−c,(v+1)/2} = {c,2c}`) is routed through `peel4c`. -/
theorem peelc_c2c (c : Nat) (hc3 : 3 ≤ c) :
    ∀ v, c + 1 ≤ v → Reach [⟨c, 2*c, c⟩] [v] [c, v - c] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hlo : v ≤ 2 * c - 2
    · have hsp : Reach [⟨c,2*c,c⟩] [v] [v / 2, (v + 1) / 2] :=
        reach_move [] (Local.nsplit v (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
      have hscat : Reach [⟨c,2*c,c⟩] [v / 2, (v + 1) / 2] (List.replicate v 1) := by
        have h := scatterList c (2*c) c [v / 2, (v + 1) / 2] (by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨by omega, by omega⟩
          · rw [List.mem_singleton] at hx; subst hx; exact ⟨by omega, by omega⟩)
        rwa [show total [v / 2, (v + 1) / 2] = v from by simp only [total_cons, total_nil]; omega] at h
      have hg1 : Reach [⟨c,2*c,c⟩] (List.replicate v 1) (c :: List.replicate (v - c) 1) :=
        gatherPrefix c (2*c) c c v (by omega) (by omega) (by omega)
      have hg2 : Reach [⟨c,2*c,c⟩] (List.replicate (v - c) 1) [v - c] := by
        have := gatherPrefix c (2*c) c (v - c) (v - c) (by omega) (by omega) (by omega); simpa using this
      have hg3 : Reach [⟨c,2*c,c⟩] (c :: List.replicate (v - c) 1) [c, v - c] := by
        have := reach_frame_left [c] hg2; simpa using this
      exact reach_trans hsp (reach_trans hscat (reach_trans hg1 hg3))
    · by_cases h1 : v = 2 * c - 1
      · refine reach_move' [] (Local.nsplit v (by omega)
          (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) ?_ (Reach.refl _)
        rw [show v / 2 = c - 1 from by omega, show (v + 1) / 2 = c from by omega, show v - c = c - 1 from by omega]
        exact List.Perm.swap (c - 1) c []
      · by_cases h2 : v = 2 * c
        · have hsp : Reach [⟨c,2*c,c⟩] [v] [v / 2, (v + 1) / 2] :=
            reach_move [] (Local.nsplit v (by omega)
              (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          rw [show v / 2 = c from by omega, show (v + 1) / 2 = c from by omega] at hsp
          rw [show v - c = c from by omega]; exact hsp
        · by_cases h3 : v = 2 * c + 1
          · have hsp : Reach [⟨c,2*c,c⟩] [v] [v / 2, (v + 1) / 2] :=
              reach_move [] (Local.nsplit v (by omega)
                (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
            rw [show v / 2 = c from by omega, show (v + 1) / 2 = c + 1 from by omega] at hsp
            rw [show v - c = c + 1 from by omega]; exact hsp
          · by_cases h4 : v = 4 * c
            · -- the lone bad value: use peel4c
              rw [h4, show 4 * c - c = 3 * c from by omega]; exact peel4c c hc3
            · -- generic recursion (v ≥ 2c+2, v ≠ 4c): merge {v/2-c, (v+1)/2} is safe
              have hsp : Reach [⟨c,2*c,c⟩] [v] [v / 2, (v + 1) / 2] :=
                reach_move [] (Local.nsplit v (by omega)
                  (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
              have hpe := ih (v / 2) (by omega) (by omega)
              have hfr : Reach [⟨c,2*c,c⟩] [v / 2, (v + 1) / 2] [c, v / 2 - c, (v + 1) / 2] := by
                have := reach_frame [(v + 1) / 2] hpe; simpa using this
              have hcc : ∀ f ∈ ([⟨c,2*c,c⟩] : Config),
                  ¬ ((f.a = v / 2 - c ∧ f.b = (v + 1) / 2) ∨ (f.a = (v + 1) / 2 ∧ f.b = v / 2 - c)) := by
                simp only [List.mem_singleton, forall_eq]; omega
              have hm0 : Reach [⟨c,2*c,c⟩] [v / 2 - c, (v + 1) / 2] [v / 2 - c + (v + 1) / 2] :=
                reach_move [] (Local.nmerge (v / 2 - c) ((v + 1) / 2) hcc) (List.Perm.refl _) (Reach.refl _)
              have hmg : Reach [⟨c,2*c,c⟩] [c, v / 2 - c, (v + 1) / 2] [c, v - c] := by
                have := reach_frame_left [c] hm0
                rw [show v / 2 - c + (v + 1) / 2 = v - c from by omega] at this
                simpa using this
              exact reach_trans hsp (reach_trans hfr hmg)

#print axioms YaStupid.peelc_c2c

end YaStupid


namespace YaStupid

/-! ### Trap pumps, parameterized by a peeler

Both peelers (`peelcG` for generic traps, `peelc_c2c` for `⟨c,2c,c⟩`) supply
`hpeel : ∀ v ≥ c+1, [v] → [c, v−c]`.  Given that, the climb/descend pumps need only:
`peelcManyG` (iterate the peel) and `powMerge` (rebuild a leg `2^k·c` from `2^k`
copies of `c` by **binary doubling** — every merge is `{x,x}→2x`, never the
forbidden pair `{a,b}` because `a ≠ b`). -/

/-- Peel `j` copies of `c` off `[v]` using any peeler `hpeel`. -/
theorem peelcManyG (a b c : Nat)
    (hpeel : ∀ v, c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] [c, v - c]) :
    ∀ j v, j * c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] (List.replicate j c ++ [v - j * c]) := by
  intro j
  induction j with
  | zero => intro v hv; simpa using Reach.refl [v]
  | succ j ih =>
    intro v hv
    have hsm : (j + 1) * c = j * c + c := by rw [Nat.succ_mul]
    have hp := hpeel v (by omega)
    have hrec := ih (v - c) (by omega)
    have hfr := reach_frame_left [c] hrec
    have e1 : c :: (List.replicate j c ++ [v - c - j * c]) = List.replicate (j + 1) c ++ [v - (j + 1) * c] := by
      rw [show v - c - j * c = v - (j + 1) * c from by omega, List.replicate_succ, List.cons_append]
    have e2 : [c] ++ (List.replicate j c ++ [v - c - j * c]) = c :: (List.replicate j c ++ [v - c - j * c]) := by simp
    rw [e2, e1] at hfr
    exact reach_trans hp hfr

/-- Rebuild `[2^k · w]` from `2^k` copies of `w` by binary doubling
    (`{x,x} → 2x`, always legal since `a ≠ b`). -/
theorem powMerge (a b c w : Nat) (hab : a ≠ b) :
    ∀ k, Reach [⟨a,b,c⟩] (List.replicate (2^k) w) [2^k * w] := by
  intro k
  induction k with
  | zero => simpa using Reach.refl [w]
  | succ k ih =>
    have hpw : 2^k * w + 2^k * w = 2^(k+1) * w := by
      rw [Nat.pow_succ, Nat.mul_comm (2^k) 2, Nat.mul_assoc, Nat.two_mul]
    have hpc : (2:Nat)^(k+1) = 2^k + 2^k := by rw [Nat.pow_succ]; omega
    have hsplit : List.replicate (2^(k+1)) w = List.replicate (2^k) w ++ List.replicate (2^k) w := by
      rw [hpc, repl_add]
    have h1 : Reach [⟨a,b,c⟩] (List.replicate (2^k) w ++ List.replicate (2^k) w)
        ([2^k * w] ++ List.replicate (2^k) w) := reach_frame _ ih
    have h2 : Reach [⟨a,b,c⟩] ([2^k * w] ++ List.replicate (2^k) w) ([2^k * w] ++ [2^k * w]) := by
      have := reach_frame_left [2^k * w] ih; simpa using this
    have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = 2^k * w ∧ f.b = 2^k * w) ∨ (f.a = 2^k * w ∧ f.b = 2^k * w)) := by
      simp only [List.mem_singleton, forall_eq]; intro h; rcases h with h | h <;> exact hab (by omega)
    have h3 : Reach [⟨a,b,c⟩] [2^k * w, 2^k * w] [2^(k+1) * w] := by
      have hm := reach_move [] (Local.nmerge (2^k * w) (2^k * w) hcc) (List.Perm.refl _) (Reach.refl _)
      rw [hpw] at hm; exact hm
    rw [hsplit]
    exact reach_trans h1 (reach_trans h2 (by simpa using h3))

#print axioms YaStupid.peelcManyG
#print axioms YaStupid.powMerge

end YaStupid


namespace YaStupid

/-! ### The trap pumps and full sufficiency, parameterized by a peeler -/

/-- **Climb pump for a trap** `⟨a,b,c⟩` (`c ≤ a`, `c ≤ b`, `c < a+b`): `[n] → [n+(a+b-c)]`
    for `n ≥ a+b+1`.  Peel a `c`, false-split `c→{a,b}`, merge back. -/
theorem climbTrap (a b c : Nat) (hc3 : 2 ≤ c) (hac : c ≤ a) (hbc : c ≤ b) (hab : c < a + b)
    (hpeel : ∀ v, c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] [c, v - c]) :
    ∀ n, a + b + 1 ≤ n → Reach [⟨a,b,c⟩] [n] [n + (a + b - c)] := by
  intro n hn
  have hp := hpeel n (by omega)
  have hfs : Reach [⟨a,b,c⟩] [c, n - c] [a, b, n - c] := by
    have hm := reach_move [n - c] (Local.fsplit ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hm1 : Reach [⟨a,b,c⟩] [a, b, n - c] [a + (n - c), b] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = a ∧ f.b = n - c) ∨ (f.a = n - c ∧ f.b = a)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm0 : Reach [⟨a,b,c⟩] [a, n - c] [a + (n - c)] :=
      reach_move [] (Local.nmerge a (n - c) hcc) (List.Perm.refl _) (Reach.refl _)
    -- [a,b,n-c] ~ [a,n-c]++[b], merge → [a+(n-c)]++[b]
    refine reach_move [b] (Local.nmerge a (n - c) hcc)
      (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
  have hm2 : Reach [⟨a,b,c⟩] [a + (n - c), b] [n + (a + b - c)] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = a + (n - c) ∧ f.b = b) ∨ (f.a = b ∧ f.b = a + (n - c))) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm0 := reach_move [] (Local.nmerge (a + (n - c)) b hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show a + (n - c) + b = n + (a + b - c) from by omega] at hm0
    exact hm0
  exact reach_trans hp (reach_trans hfs (reach_trans hm1 hm2))

/-- **Descend pump for a trap** `⟨a,b,c⟩` with `a = 2^p·c`, `b = 2^q·c`, `a ≠ b`:
    `[n+(a+b-c)] → [n]` for `n ≥ a+b+1`.  Peel `2^p+2^q` copies of `c`, rebuild
    `[a]` and `[b]` by binary doubling, false-merge `{a,b}→c`, merge back. -/
theorem descendTrap (a b c p q : Nat) (hc3 : 2 ≤ c) (hac : c ≤ a) (hbc : c ≤ b) (hab : c < a + b)
    (ha : a = 2^p * c) (hb : b = 2^q * c) (hne : a ≠ b)
    (hpeel : ∀ v, c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] [c, v - c]) :
    ∀ n, a + b + 1 ≤ n → Reach [⟨a,b,c⟩] [n + (a + b - c)] [n] := by
  intro n hn
  have hk : (2^p + 2^q) * c = a + b := by rw [ha, hb, Nat.add_mul]
  -- peel 2^p+2^q copies of c off [n+(a+b-c)]
  have hpe := peelcManyG a b c hpeel (2^p + 2^q) (n + (a + b - c)) (by rw [hk]; omega)
  rw [show n + (a + b - c) - (2^p + 2^q) * c = n - c from by rw [hk]; omega] at hpe
  -- split the c-pile into 2^p and 2^q copies
  have esplit : List.replicate (2^p + 2^q) c ++ [n - c]
      = List.replicate (2^p) c ++ (List.replicate (2^q) c ++ [n - c]) := by
    rw [← repl_add, List.append_assoc]
  rw [esplit] at hpe
  -- rebuild [a] from 2^p copies
  have ga : Reach [⟨a,b,c⟩] (List.replicate (2^p) c) [a] := by
    have := powMerge a b c c hne p; rwa [← ha] at this
  have gb : Reach [⟨a,b,c⟩] (List.replicate (2^q) c) [b] := by
    have := powMerge a b c c hne q; rwa [← hb] at this
  have g1 : Reach [⟨a,b,c⟩] (List.replicate (2^p) c ++ (List.replicate (2^q) c ++ [n - c]))
      (a :: (List.replicate (2^q) c ++ [n - c])) := by
    have := reach_frame (List.replicate (2^q) c ++ [n - c]) ga; simpa using this
  have g2 : Reach [⟨a,b,c⟩] (a :: (List.replicate (2^q) c ++ [n - c])) [a, b, n - c] := by
    have := reach_frame_left [a] (reach_frame [n - c] gb); simpa using this
  have hfm : Reach [⟨a,b,c⟩] [a, b, n - c] [c, n - c] := by
    have hm := reach_move [n - c] (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hmg : Reach [⟨a,b,c⟩] [c, n - c] [n] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = c ∧ f.b = n - c) ∨ (f.a = n - c ∧ f.b = c)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hmm := reach_move [] (Local.nmerge c (n - c) hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show c + (n - c) = n from by omega] at hmm
    exact hmm
  exact reach_trans hpe (reach_trans g1 (reach_trans g2 (reach_trans hfm hmg)))

/-- **Full sufficiency for a trap** `⟨a,b,c⟩` with `a = 2^p·c`, `b = 2^q·c`, `a ≠ b`,
    `c ≥ 3`, given a peeler.  Every `s,t ≥ M = a+b+1` with `(a+b-c) ∣ (t−s)` are
    interreachable. -/
theorem single_sufficiency_trap (a b c p q : Nat) (hc3 : 2 ≤ c) (hac : c ≤ a) (hbc : c ≤ b)
    (hab : c < a + b) (ha : a = 2^p * c) (hb : b = 2^q * c) (hne : a ≠ b)
    (hpeel : ∀ v, c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] [c, v - c]) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  have hg : gnat [⟨a,b,c⟩] = a + b - c := gnat_dpos a b c hab
  have hM : Mval [⟨a,b,c⟩] = a + b + 1 := by
    show Hnat [⟨a,b,c⟩] + 1 = a + b + 1; rw [Hnat_dpos a b c hab]
  have climb : ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]] := by
    intro n hn; rw [hg, hM] at *; exact climbTrap a b c hc3 hac hbc hab hpeel n (by omega)
  have descend : ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n] := by
    intro n hn; rw [hg, hM] at *; exact descendTrap a b c p q hc3 hac hbc hab ha hb hne hpeel n (by omega)
  intro s t hs ht hg'
  exact sufficiency_of_pumps climb descend hs ht hg'

#print axioms YaStupid.climbTrap
#print axioms YaStupid.descendTrap
#print axioms YaStupid.single_sufficiency_trap

end YaStupid


namespace YaStupid

/-! ### Swapping the false pair, and the full trap-family closure

The moves treat `{a,b}` as a set, so `⟨a,b,c⟩` and `⟨b,a,c⟩` have identical
reachability (`reach_swap`).  With that, the generic peeler (`peelcG`) and the
`⟨c,2c,c⟩` peeler (`peelc_c2c`) close **every** `c·2^k` trap `⟨c·2^p, c·2^q, c⟩`
(`p ≠ q`, `c ≥ 3`), in either leg order. -/

/-- Reachability is invariant under swapping the false pair `a ↔ b`. -/
theorem reach_swap (a b c : Nat) : ∀ {s t}, Reach [⟨a,b,c⟩] s t → Reach [⟨b,a,c⟩] s t := by
  intro s t h
  induction h with
  | refl s => exact Reach.refl s
  | @step s t u hst _ ih =>
    obtain ⟨ain, aout, rest, hl, hps, hpt⟩ := hst
    refine Reach.step ?_ ih
    cases hl with
    | nsplit n hn hc =>
      exact ⟨[n], [n/2,(n+1)/2], rest, Local.nsplit n hn
        (by simp only [List.mem_singleton, forall_eq] at hc ⊢; exact hc), hps, hpt⟩
    | fsplit f hf =>
      have hfe : f = ⟨a,b,c⟩ := by simpa using hf
      subst hfe
      refine ⟨[c], [b,a], rest, Local.fsplit ⟨b,a,c⟩ (List.mem_singleton.2 rfl), hps, ?_⟩
      exact hpt.trans (((List.Perm.swap a b []).symm).append_right rest)
    | nmerge x y hc =>
      exact ⟨[x,y],[x+y],rest, Local.nmerge x y
        (by simp only [List.mem_singleton, forall_eq] at hc ⊢; omega), hps, hpt⟩
    | fmerge f hf =>
      have hfe : f = ⟨a,b,c⟩ := by simpa using hf
      subst hfe
      refine ⟨[b,a],[c],rest, Local.fmerge ⟨b,a,c⟩ (List.mem_singleton.2 rfl), ?_, hpt⟩
      exact hps.trans (((List.Perm.swap a b []).symm).append_right rest)

/-- **The `⟨c,2c,c⟩` trap is solvable** (`c ≥ 3`): every `s,t ≥ M = 3c+1` with
    `(2c) ∣ (t−s)` are interreachable. -/
theorem single_sufficiency_c2c (c : Nat) (hc3 : 3 ≤ c) :
    ∀ s t, Mval [⟨c, 2*c, c⟩] ≤ s → Mval [⟨c, 2*c, c⟩] ≤ t →
      gz [⟨c, 2*c, c⟩] ∣ ((t : Int) - s) → Reach [⟨c, 2*c, c⟩] [s] [t] :=
  single_sufficiency_trap c (2*c) c 0 1 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (peelc_c2c c hc3)

/-- **Every generic `c·2^k` trap** `⟨2^p·c, 2^q·c, c⟩` with `|p−q| ≥ 2` or
    `min p q ≥ 1` (i.e. not the `{p,q}={0,1}` shape) is solvable. -/
theorem single_sufficiency_trap_gen (a b c p q : Nat) (hc3 : 3 ≤ c)
    (ha : a = 2^p * c) (hb : b = 2^q * c) (hac : c ≤ a) (hbc : c ≤ b) (hab : c < a + b)
    (hne : a ≠ b)
    (hsep : b ≠ a + c ∧ b ≠ a + c + 1 ∧ a ≠ b + c ∧ a ≠ b + c + 1) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] :=
  single_sufficiency_trap a b c p q (by omega) hac hbc hab ha hb hne
    (peelcG a b c (by omega) (by omega) (by omega) hbc hsep)

/-- The trap `3 + 6 = 3` (`⟨c,2c,c⟩` with `c=3`) is solvable above `M = 10`. -/
theorem solvable_3_6_3 {s t : Nat} (hs : 10 ≤ s) (ht : 10 ≤ t)
    (h : (6:Int) ∣ ((t:Int) - s)) : Reach [⟨3,6,3⟩] [s] [t] := by
  have e : ([⟨3,6,3⟩] : Config) = [⟨3, 2*3, 3⟩] := by decide
  rw [e]
  refine single_sufficiency_c2c 3 (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨3, 2*3, 3⟩] = 10 := by decide
    omega
  · have : Mval [⟨3, 2*3, 3⟩] = 10 := by decide
    omega
  · have : gz [⟨3, 2*3, 3⟩] = 6 := by decide
    rw [this]; exact h

/-- The trap `6 + 12 = 3` (`⟨2c,4c,c⟩`, `c=3`, generic) is solvable above `M = 19`. -/
theorem solvable_6_12_3 {s t : Nat} (hs : 19 ≤ s) (ht : 19 ≤ t)
    (h : (15:Int) ∣ ((t:Int) - s)) : Reach [⟨6,12,3⟩] [s] [t] := by
  refine single_sufficiency_trap_gen 6 12 3 1 2 (by omega) (by decide) (by decide)
    (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega, by omega⟩ s t ?_ ?_ ?_
  · have : Mval [⟨6,12,3⟩] = 19 := by decide
    omega
  · have : Mval [⟨6,12,3⟩] = 19 := by decide
    omega
  · have : gz [⟨6,12,3⟩] = 15 := by decide
    rw [this]; exact h

#print axioms YaStupid.reach_swap
#print axioms YaStupid.single_sufficiency_c2c
#print axioms YaStupid.single_sufficiency_trap_gen
#print axioms YaStupid.solvable_3_6_3
#print axioms YaStupid.solvable_6_12_3

end YaStupid


namespace YaStupid

/-! ### Divisible-leg descend: sequential gather (closes the both-even `c=2` traps)

For `c = 2` with both legs even (and more generally any `⟨a,b,c⟩` with `c ∣ a`,
`c ∣ b`), legs are not powers of `2·c`, so binary `powMerge` does not apply.
Rebuild a leg `m·c` by **sequential** merges `{c, k·c} → (k+1)·c` (`gatherCvalG`);
every intermediate `k·c` (`k < m`) is strictly below the leg, so the pair
`{c, k·c}` is never the forbidden `{a,b}`. -/

/-- Build `[m·c]` by sequentially merging `m` copies of `c`, given per-step safety. -/
theorem gatherCvalG (a b c : Nat) :
    ∀ m, 1 ≤ m → (∀ k, 1 ≤ k → k < m → ¬ ((a = c ∧ b = k*c) ∨ (a = k*c ∧ b = c))) →
      Reach [⟨a,b,c⟩] (List.replicate m c) [m * c] := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hsafe
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simpa using Reach.refl [c]
    · have prev := ih hmpos (fun k hk1 hk => hsafe k hk1 (by omega))
      have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = c ∧ f.b = m * c) ∨ (f.a = m * c ∧ f.b = c)) := by
        simp only [List.mem_singleton, forall_eq]; exact hsafe m (by omega) (by omega)
      have step : Reach [⟨a,b,c⟩] [c, m * c] [(m + 1) * c] := by
        have hm := reach_move [] (Local.nmerge c (m * c) hcc) (List.Perm.refl _) (Reach.refl _)
        rw [show c + m * c = (m + 1) * c from by rw [Nat.succ_mul]; omega] at hm
        exact hm
      have hfr : Reach [⟨a,b,c⟩] (c :: List.replicate m c) [c, m * c] := by
        have := reach_frame_left [c] prev; simpa using this
      rw [List.replicate_succ]
      exact reach_trans hfr step

/-- Per-step safety when the built leg `m·c = a`. -/
theorem gather_leg_safe (a b c m : Nat) (hc1 : 1 ≤ c) (hmc : m * c = a) :
    ∀ k, 1 ≤ k → k < m → ¬ ((a = c ∧ b = k*c) ∨ (a = k*c ∧ b = c)) := by
  intro k hk1 hk
  have hkc : k * c < m * c := (Nat.mul_lt_mul_right (by omega : 0 < c)).mpr hk
  have h2 : 2 * c ≤ m * c := Nat.mul_le_mul_right c (by omega)
  rw [hmc] at hkc h2
  intro hcon; rcases hcon with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-- Per-step safety when the built leg `m·c = b`. -/
theorem gather_leg_safe_b (a b c m : Nat) (hc1 : 1 ≤ c) (hmc : m * c = b) :
    ∀ k, 1 ≤ k → k < m → ¬ ((a = c ∧ b = k*c) ∨ (a = k*c ∧ b = c)) := by
  intro k hk1 hk
  have hkc : k * c < m * c := (Nat.mul_lt_mul_right (by omega : 0 < c)).mpr hk
  have h2 : 2 * c ≤ m * c := Nat.mul_le_mul_right c (by omega)
  rw [hmc] at hkc h2
  intro hcon; rcases hcon with ⟨_, h2'⟩ | ⟨_, h2'⟩ <;> omega

/-- **Divisible-leg descend.**  `⟨a,b,c⟩` with `a = ma·c`, `b = mb·c`:
    `[n+(a+b-c)] → [n]` for `n ≥ a+b+1`. -/
theorem descendSeq (a b c ma mb : Nat) (hc2 : 2 ≤ c) (hac : c ≤ a) (hbc : c ≤ b) (hab : c < a + b)
    (hma : ma * c = a) (hmb : mb * c = b) (hma1 : 1 ≤ ma) (hmb1 : 1 ≤ mb)
    (hpeel : ∀ v, c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] [c, v - c]) :
    ∀ n, a + b + 1 ≤ n → Reach [⟨a,b,c⟩] [n + (a + b - c)] [n] := by
  intro n hn
  have hk : (ma + mb) * c = a + b := by rw [Nat.add_mul, hma, hmb]
  have hpe := peelcManyG a b c hpeel (ma + mb) (n + (a + b - c)) (by rw [hk]; omega)
  rw [show n + (a + b - c) - (ma + mb) * c = n - c from by rw [hk]; omega] at hpe
  have esplit : List.replicate (ma + mb) c ++ [n - c]
      = List.replicate ma c ++ (List.replicate mb c ++ [n - c]) := by
    rw [← repl_add, List.append_assoc]
  rw [esplit] at hpe
  have ga : Reach [⟨a,b,c⟩] (List.replicate ma c) [a] := by
    have := gatherCvalG a b c ma hma1 (gather_leg_safe a b c ma (by omega) hma); rwa [hma] at this
  have gb : Reach [⟨a,b,c⟩] (List.replicate mb c) [b] := by
    have := gatherCvalG a b c mb hmb1 (gather_leg_safe_b a b c mb (by omega) hmb); rwa [hmb] at this
  have g1 : Reach [⟨a,b,c⟩] (List.replicate ma c ++ (List.replicate mb c ++ [n - c]))
      (a :: (List.replicate mb c ++ [n - c])) := by
    have := reach_frame (List.replicate mb c ++ [n - c]) ga; simpa using this
  have g2 : Reach [⟨a,b,c⟩] (a :: (List.replicate mb c ++ [n - c])) [a, b, n - c] := by
    have := reach_frame_left [a] (reach_frame [n - c] gb); simpa using this
  have hfm : Reach [⟨a,b,c⟩] [a, b, n - c] [c, n - c] := by
    have hm := reach_move [n - c] (Local.fmerge ⟨a,b,c⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hmg : Reach [⟨a,b,c⟩] [c, n - c] [n] := by
    have hcc : ∀ f ∈ ([⟨a,b,c⟩] : Config), ¬ ((f.a = c ∧ f.b = n - c) ∨ (f.a = n - c ∧ f.b = c)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hmm := reach_move [] (Local.nmerge c (n - c) hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show c + (n - c) = n from by omega] at hmm
    exact hmm
  exact reach_trans hpe (reach_trans g1 (reach_trans g2 (reach_trans hfm hmg)))

/-- **Full sufficiency for any divisible-leg config** `⟨a,b,c⟩` (`c ≥ 2`, `c ∣ a`,
    `c ∣ b`, given a peeler).  Closes the both-even `c=2` traps. -/
theorem single_sufficiency_div (a b c ma mb : Nat) (hc2 : 2 ≤ c) (hac : c ≤ a) (hbc : c ≤ b)
    (hab : c < a + b) (hma : ma * c = a) (hmb : mb * c = b) (hma1 : 1 ≤ ma) (hmb1 : 1 ≤ mb)
    (hpeel : ∀ v, c + 1 ≤ v → Reach [⟨a,b,c⟩] [v] [c, v - c]) :
    ∀ s t, Mval [⟨a,b,c⟩] ≤ s → Mval [⟨a,b,c⟩] ≤ t →
      gz [⟨a,b,c⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,c⟩] [s] [t] := by
  have hg : gnat [⟨a,b,c⟩] = a + b - c := gnat_dpos a b c hab
  have hM : Mval [⟨a,b,c⟩] = a + b + 1 := by
    show Hnat [⟨a,b,c⟩] + 1 = a + b + 1; rw [Hnat_dpos a b c hab]
  have climb : ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n] [n + gnat [⟨a,b,c⟩]] := by
    intro n hn; rw [hg, hM] at *; exact climbTrap a b c hc2 hac hbc hab hpeel n (by omega)
  have descend : ∀ n, Mval [⟨a,b,c⟩] ≤ n → Reach [⟨a,b,c⟩] [n + gnat [⟨a,b,c⟩]] [n] := by
    intro n hn; rw [hg, hM] at *; exact descendSeq a b c ma mb hc2 hac hbc hab hma hmb hma1 hmb1 hpeel n (by omega)
  intro s t hs ht hg'
  exact sufficiency_of_pumps climb descend hs ht hg'

#print axioms YaStupid.gatherCvalG
#print axioms YaStupid.descendSeq
#print axioms YaStupid.single_sufficiency_div

end YaStupid


namespace YaStupid

/-! ### Closing the both-even `c=2` traps

For `c = 2` with both legs even (`a = 2·ma`, `b = 2·mb`) the all-ones field is
unreachable (tapping a `2` only yields `{a,b}`, both even — the pile never reaches
an odd number).  The escape is the *copies-of-`2`* hub: `peelcG` peels a `2`, and
`descendSeq` rebuilds the legs from `2`s.  Whenever `|a−b| ∉ {2,3}` (so the peel
recursion is coincidence-free) this closes the config — e.g. `4+4=2`, `6+6=2`,
`4+8=2`. -/

/-- **Both-even `c=2` traps with `|a−b| ∉ {2,3}` are solvable.** -/
theorem single_sufficiency_c2_even (a b ma mb : Nat) (ha : ma * 2 = a) (hb : mb * 2 = b)
    (hma1 : 1 ≤ ma) (hmb1 : 1 ≤ mb) (hab : 2 < a + b)
    (hsep : b ≠ a + 2 ∧ b ≠ a + 2 + 1 ∧ a ≠ b + 2 ∧ a ≠ b + 2 + 1) :
    ∀ s t, Mval [⟨a,b,2⟩] ≤ s → Mval [⟨a,b,2⟩] ≤ t →
      gz [⟨a,b,2⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,2⟩] [s] [t] := by
  have hpeel := peelcG a b 2 (by omega) (by omega) (by omega) (by omega) hsep
  exact single_sufficiency_div a b 2 ma mb (by omega) (by omega) (by omega) hab ha hb hma1 hmb1 hpeel

/-- The trap `4 + 4 = 2` (both legs even; no ones reachable) is solvable above `M = 9`. -/
theorem solvable_4_4_2 {s t : Nat} (hs : 9 ≤ s) (ht : 9 ≤ t)
    (h : (6:Int) ∣ ((t:Int) - s)) : Reach [⟨4,4,2⟩] [s] [t] := by
  refine single_sufficiency_c2_even 4 4 2 2 (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨by omega, by omega, by omega, by omega⟩ s t ?_ ?_ ?_
  · have : Mval [⟨4,4,2⟩] = 9 := by decide
    omega
  · have : Mval [⟨4,4,2⟩] = 9 := by decide
    omega
  · have : gz [⟨4,4,2⟩] = 6 := by decide
    rw [this]; exact h

/-- The trap `4 + 8 = 2` (both even, `|a−b| = 4`) is solvable above `M = 13`. -/
theorem solvable_4_8_2 {s t : Nat} (hs : 13 ≤ s) (ht : 13 ≤ t)
    (h : (10:Int) ∣ ((t:Int) - s)) : Reach [⟨4,8,2⟩] [s] [t] := by
  refine single_sufficiency_c2_even 4 8 2 4 (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨by omega, by omega, by omega, by omega⟩ s t ?_ ?_ ?_
  · have : Mval [⟨4,8,2⟩] = 13 := by decide
    omega
  · have : Mval [⟨4,8,2⟩] = 13 := by decide
    omega
  · have : gz [⟨4,8,2⟩] = 10 := by decide
    rw [this]; exact h

#print axioms YaStupid.single_sufficiency_c2_even
#print axioms YaStupid.solvable_4_4_2
#print axioms YaStupid.solvable_4_8_2

end YaStupid


namespace YaStupid

/-! ### A uniform peeler for `c = 2` (both legs `≥ 3`): `peelc2`

For `c = 2` the all-ones field is generally out of reach, and `peelcG`'s recursion
can hit the forbidden pair when `|a−b| ∈ {2,3}`.  `peelc2` sidesteps this: at the
recursion step `[v] → [2, v/2−2, (v+1)/2]`, if the merge `{v/2−2, (v+1)/2}` would
be `{a,b}` (which forces `|a−b| ∈ {2,3}`), peel a `2` off the *other* half too and
merge the two near-equal residues `{v/2−2, (v+1)/2−2}` (they differ by `≤ 1`, hence
never `{a,b}` once `|a−b| ≥ 2`), then merge in a `2`.  Legs `≥ 3` keep every
`{2, ·}` merge clean. -/

/-- Peel a `2` off any `v ≥ 3` in `⟨a,b,2⟩` with both legs `≥ 3`. -/
theorem peelc2 (a b : Nat) (ha3 : 3 ≤ a) (hb3 : 3 ≤ b) :
    ∀ v, 3 ≤ v → Reach [⟨a,b,2⟩] [v] [2, v - 2] := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases h3 : v = 3
    · subst h3
      refine reach_move' [] (Local.nsplit 3 (by omega) (by simp only [List.mem_singleton, forall_eq]; omega))
        (List.Perm.refl _) ?_ (Reach.refl _)
      exact List.Perm.swap 1 2 []
    · by_cases h4 : v = 4
      · subst h4
        have h : Reach [⟨a,b,2⟩] [4] [4/2, (4+1)/2] :=
          reach_move [] (Local.nsplit 4 (by omega) (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
        simpa using h
      · by_cases h5 : v = 5
        · subst h5
          have h : Reach [⟨a,b,2⟩] [5] [5/2, (5+1)/2] :=
            reach_move [] (Local.nsplit 5 (by omega) (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          simpa using h
        · -- v ≥ 6
          have hsp : Reach [⟨a,b,2⟩] [v] [v/2, (v+1)/2] :=
            reach_move [] (Local.nsplit v (by omega) (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
          have hp1 := ih (v/2) (by omega) (by omega)
          have hfr1 : Reach [⟨a,b,2⟩] [v/2, (v+1)/2] [2, v/2 - 2, (v+1)/2] := by
            have := reach_frame [(v+1)/2] hp1; simpa using this
          by_cases hbad : (a = v/2 - 2 ∧ b = (v+1)/2) ∨ (a = (v+1)/2 ∧ b = v/2 - 2)
          · -- alternate route: peel 2 off the other half too
            have hp2 := ih ((v+1)/2) (by omega) (by omega)
            have hfr2 : Reach [⟨a,b,2⟩] [2, v/2 - 2, (v+1)/2] [2, v/2 - 2, 2, (v+1)/2 - 2] := by
              have := reach_frame_left [2, v/2 - 2] hp2; simpa using this
            have hmid : Reach [⟨a,b,2⟩] [2, v/2 - 2, 2, (v+1)/2 - 2] [v - 4, 2, 2] := by
              have hcc : ∀ f ∈ ([⟨a,b,2⟩] : Config),
                  ¬ ((f.a = v/2 - 2 ∧ f.b = (v+1)/2 - 2) ∨ (f.a = (v+1)/2 - 2 ∧ f.b = v/2 - 2)) := by
                rcases hbad with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;> (simp only [List.mem_singleton, forall_eq]; omega)
              have h : Reach [⟨a,b,2⟩] [2, v/2 - 2, 2, (v+1)/2 - 2] ([(v/2 - 2) + ((v+1)/2 - 2)] ++ [2,2]) :=
                reach_move [2,2] (Local.nmerge (v/2 - 2) ((v+1)/2 - 2) hcc)
                  (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) (Reach.refl _)
              rw [show (v/2 - 2) + ((v+1)/2 - 2) = v - 4 from by omega] at h; exact h
            have hfin : Reach [⟨a,b,2⟩] [v - 4, 2, 2] [2, v - 2] := by
              have hcc : ∀ f ∈ ([⟨a,b,2⟩] : Config), ¬ ((f.a = v - 4 ∧ f.b = 2) ∨ (f.a = 2 ∧ f.b = v - 4)) := by
                simp only [List.mem_singleton, forall_eq]; omega
              refine reach_move' [2] (Local.nmerge (v - 4) 2 hcc)
                (by rw [List.perm_iff_count]; intro x; simp [List.count_cons] <;> omega) ?_ (Reach.refl _)
              rw [show (v - 4) + 2 = v - 2 from by omega]
              exact List.Perm.swap (v - 2) 2 []
            exact reach_trans hsp (reach_trans hfr1 (reach_trans hfr2 (reach_trans hmid hfin)))
          · -- normal route
            have hcc : ∀ f ∈ ([⟨a,b,2⟩] : Config),
                ¬ ((f.a = v/2 - 2 ∧ f.b = (v+1)/2) ∨ (f.a = (v+1)/2 ∧ f.b = v/2 - 2)) := by
              simp only [List.mem_singleton, forall_eq]; exact hbad
            have hm0 : Reach [⟨a,b,2⟩] [v/2 - 2, (v+1)/2] [v/2 - 2 + (v+1)/2] :=
              reach_move [] (Local.nmerge (v/2 - 2) ((v+1)/2) hcc) (List.Perm.refl _) (Reach.refl _)
            have hmg : Reach [⟨a,b,2⟩] [2, v/2 - 2, (v+1)/2] [2, v - 2] := by
              have := reach_frame_left [2] hm0
              rw [show v/2 - 2 + (v+1)/2 = v - 2 from by omega] at this
              simpa using this
            exact reach_trans hsp (reach_trans hfr1 hmg)

#print axioms YaStupid.peelc2

end YaStupid


namespace YaStupid

/-- **All both-even `c=2` traps with legs `≥ 3` are solvable** (any `|a−b|`), via the
    copies-of-`2` hub `peelc2` + `descendSeq`. -/
theorem single_sufficiency_c2_both_even (a b ma mb : Nat) (ha3 : 3 ≤ a) (hb3 : 3 ≤ b)
    (ha : ma * 2 = a) (hb : mb * 2 = b) (hma1 : 1 ≤ ma) (hmb1 : 1 ≤ mb) (hab : 2 < a + b) :
    ∀ s t, Mval [⟨a,b,2⟩] ≤ s → Mval [⟨a,b,2⟩] ≤ t →
      gz [⟨a,b,2⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,2⟩] [s] [t] :=
  single_sufficiency_div a b 2 ma mb (by omega) (by omega) (by omega) hab ha hb hma1 hmb1
    (peelc2 a b ha3 hb3)

/-- The trap `4 + 6 = 2` (both even, `b = a+2` — the previously-stuck adjacent case)
    is solvable above `M = 11`. -/
theorem solvable_4_6_2 {s t : Nat} (hs : 11 ≤ s) (ht : 11 ≤ t)
    (h : (8:Int) ∣ ((t:Int) - s)) : Reach [⟨4,6,2⟩] [s] [t] := by
  refine single_sufficiency_c2_both_even 4 6 2 3 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨4,6,2⟩] = 11 := by decide
    omega
  · have : Mval [⟨4,6,2⟩] = 11 := by decide
    omega
  · have : gz [⟨4,6,2⟩] = 8 := by decide
    rw [this]; exact h

#print axioms YaStupid.single_sufficiency_c2_both_even
#print axioms YaStupid.solvable_4_6_2

end YaStupid


namespace YaStupid

/-! ### `c = 2` with `a = b` (any parity): `single_sufficiency_c2_aa`

When `a = b` (and `c = 2`), descend works even for *odd* `a` (where `descendSeq`
fails, `2 ∤ a`): build `[2a]` from `a` copies of `2` (sequential gather, safe since
`a ≥ 3 ⇒ 2 ∉ {a}`), **split** `[2a] → {a,a}` (normal, `2a ≠ 2`), then false-merge
`{a,a} → 2`.  No `1`s, no power-of-`2` obstruction. -/

/-- Descend for `⟨a,a,2⟩` (`a ≥ 3`): `[n+(2a-2)] → [n]`. -/
theorem descendAA2 (a : Nat) (ha3 : 3 ≤ a)
    (hpeel : ∀ v, 3 ≤ v → Reach [⟨a,a,2⟩] [v] [2, v - 2]) :
    ∀ n, a + a + 1 ≤ n → Reach [⟨a,a,2⟩] [n + (a + a - 2)] [n] := by
  intro n hn
  have hpe := peelcManyG a a 2 hpeel a (n + (a + a - 2)) (by omega)
  rw [show n + (a + a - 2) - a * 2 = n - 2 from by omega] at hpe
  -- gather the a copies of 2 into [2a]
  have hgs : ∀ k, 1 ≤ k → k < a → ¬ ((a = 2 ∧ a = k*2) ∨ (a = k*2 ∧ a = 2)) := by
    intro k _ _; omega
  have hga : Reach [⟨a,a,2⟩] (List.replicate a 2) [a * 2] := gatherCvalG a a 2 a (by omega) hgs
  have g1 : Reach [⟨a,a,2⟩] (List.replicate a 2 ++ [n - 2]) ([a * 2] ++ [n - 2]) := reach_frame _ hga
  -- split [2a] -> [a,a]
  have hsplit : Reach [⟨a,a,2⟩] [a * 2] [a, a] := by
    have h : Reach [⟨a,a,2⟩] [a * 2] [(a*2)/2, (a*2+1)/2] :=
      reach_move [] (Local.nsplit (a*2) (by omega) (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    rwa [show (a*2)/2 = a from by omega, show (a*2+1)/2 = a from by omega] at h
  have g2 : Reach [⟨a,a,2⟩] ([a * 2] ++ [n - 2]) [a, a, n - 2] := by
    have := reach_frame [n - 2] hsplit; simpa using this
  have hfm : Reach [⟨a,a,2⟩] [a, a, n - 2] [2, n - 2] := by
    have hm := reach_move [n - 2] (Local.fmerge ⟨a,a,2⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hmg : Reach [⟨a,a,2⟩] [2, n - 2] [n] := by
    have hcc : ∀ f ∈ ([⟨a,a,2⟩] : Config), ¬ ((f.a = 2 ∧ f.b = n - 2) ∨ (f.a = n - 2 ∧ f.b = 2)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hmm := reach_move [] (Local.nmerge 2 (n - 2) hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show 2 + (n - 2) = n from by omega] at hmm
    exact hmm
  exact reach_trans hpe (reach_trans g1 (reach_trans g2 (reach_trans hfm hmg)))

/-- **`⟨a,a,2⟩` is solvable for every `a ≥ 3`** (both parities; e.g. `3+3=2`, `5+5=2`). -/
theorem single_sufficiency_c2_aa (a : Nat) (ha3 : 3 ≤ a) :
    ∀ s t, Mval [⟨a,a,2⟩] ≤ s → Mval [⟨a,a,2⟩] ≤ t →
      gz [⟨a,a,2⟩] ∣ ((t : Int) - s) → Reach [⟨a,a,2⟩] [s] [t] := by
  have hpeel := peelc2 a a ha3 ha3
  have hg : gnat [⟨a,a,2⟩] = a + a - 2 := gnat_dpos a a 2 (by omega)
  have hM : Mval [⟨a,a,2⟩] = a + a + 1 := by
    show Hnat [⟨a,a,2⟩] + 1 = a + a + 1; rw [Hnat_dpos a a 2 (by omega)]
  have climb : ∀ n, Mval [⟨a,a,2⟩] ≤ n → Reach [⟨a,a,2⟩] [n] [n + gnat [⟨a,a,2⟩]] := by
    intro n hn; rw [hg, hM] at *; exact climbTrap a a 2 (by omega) (by omega) (by omega) (by omega) hpeel n (by omega)
  have descend : ∀ n, Mval [⟨a,a,2⟩] ≤ n → Reach [⟨a,a,2⟩] [n + gnat [⟨a,a,2⟩]] [n] := by
    intro n hn; rw [hg, hM] at *; exact descendAA2 a ha3 hpeel n (by omega)
  intro s t hs ht hg'
  exact sufficiency_of_pumps climb descend hs ht hg'

/-- The trap `3 + 3 = 2` (odd legs, `a=b`; `descendSeq` does not apply) is solvable
    above `M = 7`. -/
theorem solvable_3_3_2 {s t : Nat} (hs : 7 ≤ s) (ht : 7 ≤ t)
    (h : (4:Int) ∣ ((t:Int) - s)) : Reach [⟨3,3,2⟩] [s] [t] := by
  refine single_sufficiency_c2_aa 3 (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨3,3,2⟩] = 7 := by decide
    omega
  · have : Mval [⟨3,3,2⟩] = 7 := by decide
    omega
  · have : gz [⟨3,3,2⟩] = 4 := by decide
    rw [this]; exact h

#print axioms YaStupid.descendAA2
#print axioms YaStupid.single_sufficiency_c2_aa
#print axioms YaStupid.solvable_3_3_2

end YaStupid


namespace YaStupid

/-! ### `c = 2` with both legs odd, `a ≠ b`: `single_sufficiency_c2_both_odd`

Both legs odd ⇒ `b − a` even, say `b = a + 2d`.  Descend needs no `1`s: build `[2a]`
from `a` copies of `2`, **split** `[2a] → [a,a]`, keep one `[a]`, and bridge the other
to `[b]` by merging in `d` more `2`s (`{x,2}` is never `{a,b}` since legs `≥ 3`).
Then false-merge `{a,b} → 2`. -/

/-- Merge `d` copies of `2` onto a ball `[x]` (legal in `⟨a,b,2⟩`, legs `≥ 3`). -/
theorem mergeTwos (a b : Nat) (ha3 : 3 ≤ a) (hb3 : 3 ≤ b) :
    ∀ d x, Reach [⟨a,b,2⟩] (x :: List.replicate d 2) [x + 2 * d] := by
  intro d
  induction d with
  | zero => intro x; simpa using Reach.refl [x]
  | succ d ih =>
    intro x
    have hcc : ∀ f ∈ ([⟨a,b,2⟩] : Config), ¬ ((f.a = x ∧ f.b = 2) ∨ (f.a = 2 ∧ f.b = x)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hm : Reach [⟨a,b,2⟩] (x :: List.replicate (d+1) 2) ((x + 2) :: List.replicate d 2) := by
      have h : Reach [⟨a,b,2⟩] ([x, 2] ++ List.replicate d 2) ([x + 2] ++ List.replicate d 2) :=
        reach_frame (List.replicate d 2) (reach_move [] (Local.nmerge x 2 hcc) (List.Perm.refl _) (Reach.refl _))
      have e1 : x :: List.replicate (d+1) 2 = [x, 2] ++ List.replicate d 2 := by
        rw [List.replicate_succ]; rfl
      rw [e1]; simpa using h
    have hrec := ih (x + 2)
    rw [show x + 2 * (d + 1) = (x + 2) + 2 * d from by omega]
    exact reach_trans hm hrec

/-- Descend for both-odd `⟨a,b,2⟩` with `b = a + 2d` (`a ≥ 3`, `d ≥ 1`):
    `[n+(a+b-2)] → [n]`. -/
theorem descendBothOdd2 (a b d : Nat) (ha3 : 3 ≤ a) (hb3 : 3 ≤ b) (hd1 : 1 ≤ d)
    (hb : b = a + 2*d) (hpeel : ∀ v, 3 ≤ v → Reach [⟨a,b,2⟩] [v] [2, v - 2]) :
    ∀ n, a + b + 1 ≤ n → Reach [⟨a,b,2⟩] [n + (a + b - 2)] [n] := by
  intro n hn
  have hpe := peelcManyG a b 2 hpeel (a + d) (n + (a + b - 2)) (by omega)
  rw [show n + (a + b - 2) - (a + d) * 2 = n - 2 from by omega] at hpe
  have esplit : List.replicate (a + d) 2 ++ [n - 2]
      = List.replicate a 2 ++ (List.replicate d 2 ++ [n - 2]) := by
    rw [← repl_add, List.append_assoc]
  rw [esplit] at hpe
  have hgs : ∀ k, 1 ≤ k → k < a → ¬ ((a = 2 ∧ b = k*2) ∨ (a = k*2 ∧ b = 2)) := by
    intro k _ _; omega
  have hga : Reach [⟨a,b,2⟩] (List.replicate a 2) [a * 2] := gatherCvalG a b 2 a (by omega) hgs
  have hsplit : Reach [⟨a,b,2⟩] [a * 2] [a, a] := by
    have h : Reach [⟨a,b,2⟩] [a * 2] [(a*2)/2, (a*2+1)/2] :=
      reach_move [] (Local.nsplit (a*2) (by omega) (by simp only [List.mem_singleton, forall_eq]; omega)) (List.Perm.refl _) (Reach.refl _)
    rwa [show (a*2)/2 = a from by omega, show (a*2+1)/2 = a from by omega] at h
  have gaa : Reach [⟨a,b,2⟩] (List.replicate a 2) [a, a] := reach_trans hga hsplit
  have g1 : Reach [⟨a,b,2⟩] (List.replicate a 2 ++ (List.replicate d 2 ++ [n - 2]))
      ([a, a] ++ (List.replicate d 2 ++ [n - 2])) := reach_frame _ gaa
  have hbridge : Reach [⟨a,b,2⟩] (a :: List.replicate d 2) [b] := by
    have := mergeTwos a b ha3 hb3 d a; rwa [show a + 2 * d = b from by omega] at this
  have g2 : Reach [⟨a,b,2⟩] ([a, a] ++ (List.replicate d 2 ++ [n - 2])) [a, b, n - 2] := by
    have hb2 : Reach [⟨a,b,2⟩] (a :: List.replicate d 2 ++ [n - 2]) (b :: [n - 2]) := by
      have := reach_frame [n - 2] hbridge; simpa using this
    have := reach_frame_left [a] hb2
    simpa using this
  have hfm : Reach [⟨a,b,2⟩] [a, b, n - 2] [2, n - 2] := by
    have hm := reach_move [n - 2] (Local.fmerge ⟨a,b,2⟩ (List.mem_singleton.2 rfl)) (List.Perm.refl _) (Reach.refl _)
    simpa using hm
  have hmg : Reach [⟨a,b,2⟩] [2, n - 2] [n] := by
    have hcc : ∀ f ∈ ([⟨a,b,2⟩] : Config), ¬ ((f.a = 2 ∧ f.b = n - 2) ∨ (f.a = n - 2 ∧ f.b = 2)) := by
      simp only [List.mem_singleton, forall_eq]; omega
    have hmm := reach_move [] (Local.nmerge 2 (n - 2) hcc) (List.Perm.refl _) (Reach.refl _)
    rw [show 2 + (n - 2) = n from by omega] at hmm
    exact hmm
  exact reach_trans hpe (reach_trans g1 (reach_trans g2 (reach_trans hfm hmg)))

/-- **Both-odd `⟨a,b,2⟩` (`b = a+2d`) is solvable** (`a ≥ 3`, `d ≥ 1`; e.g. `3+5=2`,
    `3+7=2`, `5+7=2`). -/
theorem single_sufficiency_c2_both_odd (a b d : Nat) (ha3 : 3 ≤ a) (hb3 : 3 ≤ b) (hd1 : 1 ≤ d)
    (hb : b = a + 2*d) :
    ∀ s t, Mval [⟨a,b,2⟩] ≤ s → Mval [⟨a,b,2⟩] ≤ t →
      gz [⟨a,b,2⟩] ∣ ((t : Int) - s) → Reach [⟨a,b,2⟩] [s] [t] := by
  have hpeel := peelc2 a b ha3 hb3
  have hg : gnat [⟨a,b,2⟩] = a + b - 2 := gnat_dpos a b 2 (by omega)
  have hM : Mval [⟨a,b,2⟩] = a + b + 1 := by
    show Hnat [⟨a,b,2⟩] + 1 = a + b + 1; rw [Hnat_dpos a b 2 (by omega)]
  have climb : ∀ n, Mval [⟨a,b,2⟩] ≤ n → Reach [⟨a,b,2⟩] [n] [n + gnat [⟨a,b,2⟩]] := by
    intro n hn; rw [hg, hM] at *; exact climbTrap a b 2 (by omega) (by omega) (by omega) (by omega) hpeel n (by omega)
  have descend : ∀ n, Mval [⟨a,b,2⟩] ≤ n → Reach [⟨a,b,2⟩] [n + gnat [⟨a,b,2⟩]] [n] := by
    intro n hn; rw [hg, hM] at *; exact descendBothOdd2 a b d ha3 hb3 hd1 hb hpeel n (by omega)
  intro s t hs ht hg'
  exact sufficiency_of_pumps climb descend hs ht hg'

/-- The trap `3 + 5 = 2` (both odd, `a ≠ b`) is solvable above `M = 9`. -/
theorem solvable_3_5_2 {s t : Nat} (hs : 9 ≤ s) (ht : 9 ≤ t)
    (h : (6:Int) ∣ ((t:Int) - s)) : Reach [⟨3,5,2⟩] [s] [t] := by
  refine single_sufficiency_c2_both_odd 3 5 1 (by omega) (by omega) (by omega) (by omega) s t ?_ ?_ ?_
  · have : Mval [⟨3,5,2⟩] = 9 := by decide
    omega
  · have : Mval [⟨3,5,2⟩] = 9 := by decide
    omega
  · have : gz [⟨3,5,2⟩] = 6 := by decide
    rw [this]; exact h

#print axioms YaStupid.descendBothOdd2
#print axioms YaStupid.single_sufficiency_c2_both_odd
#print axioms YaStupid.solvable_3_5_2

end YaStupid
