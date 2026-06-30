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

#print axioms YaStupid.gatherMin1
#print axioms YaStupid.loseGmin1
#print axioms YaStupid.baseD_dneg_min1
#print axioms YaStupid.single_sufficiency_dneg_min1
#print axioms YaStupid.single_sufficiency_dpos
#print axioms YaStupid.solvable_3_3_5
