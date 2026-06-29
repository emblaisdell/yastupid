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
  exact Dvd.dvd.trans h (Int.natAbs_dvd.1 (dvd_refl _))

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
    have hsplit : (total u : Int) - total s
        = ((total u : Int) - total t) + ((total t : Int) - total s) := by omega
    rw [hsplit]; exact dvd_add ih h1

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
      intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with h | h <;> omega
    refine ⟨pos_perm hpt.symm (pos_append haout hposrest), ?_⟩
    rcases hval with hv | hv
    · left; omega
    · exfalso
      have heq : n :: rest = [21] := by simpa using List.perm_singleton.1 (hps.symm.trans hv)
      injection heq with hn21 hrest
      exact (hc ⟨9, 10, 21⟩ (by simp [classic])) hn21
  | fsplit f hf =>
    have hfe : f = ⟨9, 10, 21⟩ := by simpa [classic] using hf
    subst hfe
    have hts : total s = 21 + total rest := by
      rw [total_perm hps, total_append]; simp only [total_cons, total_nil]; omega
    have htt : total t = 19 + total rest := by
      rw [total_perm hpt, total_append]; simp only [total_cons, total_nil]; omega
    have haout : Pos [9, 10] := by
      intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with h | h <;> omega
    refine ⟨pos_perm hpt.symm (pos_append haout hposrest), ?_⟩
    rcases hval with hv | hv
    · exfalso; omega
    · have hlen := (hps.symm.trans hv).length_eq
      simp only [List.length_append, List.length_cons, List.length_singleton,
        List.length_nil] at hlen
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
      simp only [List.length_append, List.length_cons, List.length_singleton,
        List.length_nil] at hlen
      omega
  | fmerge f hf =>
    have hfe : f = ⟨9, 10, 21⟩ := by simpa [classic] using hf
    subst hfe
    have hts : total s = 19 + total rest := by
      rw [total_perm hps, total_append]; simp only [total_cons, total_nil]; omega
    have haout : Pos [21] := by intro z hz; simp only [List.mem_singleton] at hz; omega
    refine ⟨pos_perm hpt.symm (pos_append haout hposrest), ?_⟩
    rcases hval with hv | hv
    · have hr : rest = [] := pos_total_zero hposrest (by omega)
      subst hr; right; simpa using hpt
    · exfalso
      have hlen := (hps.symm.trans hv).length_eq
      simp only [List.length_append, List.length_cons, List.length_singleton,
        List.length_nil] at hlen
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
  · simp only [total_cons, total_nil] at h19
  · have : (23 : Nat) = 21 := by simpa using List.perm_singleton.1 hp
    omega

end YaStupid
