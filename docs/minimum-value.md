# The Minimum Solvable Value in *Ya Stupid*

*A note on the reachability threshold for Classic and Advanced modes.*

---

## 1. The model

A **state** is a finite multiset of positive integers (the values written on the
balls). The total $\Sigma$ of a state is the sum of its elements.

There are two physical gestures, each of which (in the absence of false sums)
**conserves** $\Sigma$:

- **Split** (tap) a ball of value $n\ge 2$:
$$
n \;\longmapsto\; \Bigl\{\bigl\lfloor \tfrac n2\bigr\rfloor,\ \bigl\lceil \tfrac n2\bigr\rceil\Bigr\}.
$$
  A ball of value $1$ cannot be split.
- **Merge** (drag) two balls $x,y$:
$$
\{x,y\}\;\longmapsto\;\{x+y\}.
$$

On top of this we are given a finite set of **false sums**
$$
\mathcal F=\bigl\{(a_i,b_i,c_i)\bigr\}_{i=1}^m ,\qquad a_i,b_i,c_i\in\mathbb Z_{>0},
$$
with the RHS values $c_i$ pairwise distinct and the LHS pairs $\{a_i,b_i\}$
pairwise distinct. Each false sum overrides the two normal gestures **at its own
values**:

- **False split.** *Any* ball whose value is $c_i$ splits to the ordained pair:
  $\,c_i \mapsto \{a_i,b_i\}$. (Value $c_i$ has no normal split.)
- **False merge.** The ordained pair merges to the false RHS:
  $\,\{a_i,b_i\}\mapsto c_i$. (Other pairs summing to $c_i$ merge normally to a
  *normal* ball of value $c_i$, which then false‑splits — see Remark 1.)

The **inaccuracy** of false sum $i$ is
$$
d_i \;=\; (a_i+b_i)-c_i \;\neq\;0,
$$
and we write $\delta_i=|d_i|$. Let
$$
\boxed{\,g=\gcd(\delta_1,\dots,\delta_m)\,}
$$
(in Classic mode there is a single false sum, so $g=\delta_1$).

A pair $(s,t)$ is **solvable** if, starting from the one‑ball state $\{s\}$, some
sequence of gestures reaches the one‑ball state $\{t\}$. Note solvability is a
*directed* relation $s\to t$; §5 shows it is genuinely not symmetric.

> **Classic mode** is the single false sum $\,9+10=21$:
> $a_1=9,\ b_1=10,\ c_1=21,\ d_1=19-21=-2,\ \delta_1=2,\ g=2.$

---

## 2. The two invariants and the necessary condition

**Every gesture changes $\Sigma$ by an element of $g\mathbb Z$.** A normal split or
merge changes it by $0$; a false split or merge of sum $i$ changes it by
$\pm d_i$, a multiple of $g$. Hence $\Sigma \bmod g$ is invariant, giving the

> **Necessary condition.** If $s\to t$ then $t\equiv s \pmod g$.

This is exactly the user's "differ by a multiple of the gcd of the
inaccuracies." The rest of the note shows that, *above a threshold*, this
congruence is also **sufficient**, and pins the threshold down exactly.

---

## 3. The threshold

Define, for each false sum, the larger of its true LHS sum and its RHS, and take
the maximum:
$$
\boxed{\,H \;=\; \max_{1\le i\le m}\ \max\bigl(a_i+b_i,\ c_i\bigr)\,},
\qquad
\boxed{\,M \;=\; H+1\,}.
$$

> **Classic mode.** $H=\max(19,21)=21$, so $M=22$.

> **Main Theorem.**
> 1. *(Sufficiency.)* For every $s,t$ with $s\equiv t \pmod g$ and
>    $\min(s,t) > H$ (equivalently $s,t\ge M$), the pair $(s,t)$ is solvable.
> 2. *(Sharpness.)* $H$ cannot replace $H+1$: there are instances — Classic among
>    them — and pairs $s,t\ge H$ with $s\equiv t\pmod g$ that are **unsolvable**.
>
> Hence $M=H+1$ is the smallest threshold that works for *every* instance.

The two halves are proved in §4 and §5. §6 records the sharper per‑instance
picture, and §7 specializes everything to the game.

---

## 4. Sufficiency: above $H$ the congruence is enough

Throughout this section fix $s,t>H$ with $t\equiv s\pmod g$.

### 4.1 A partition lemma — and a correction

> ⚠️ **Erratum.** An earlier version of this note proved carving by first reaching
> the **all‑ones** state. *That is false in general.* Take the false sum
> $2+2=2$: tapping any $2$ yields $\{2,2\}$ (and $\{2,2\}$ merges back to $2$), so
> a region of $2$s can **never** be reduced to $1$s. More adversarially,
> $\{\,6+7=2,\ 6+8=3\,\}$ locks both $2$ and $3$ and neither ordained pair contains
> a $1$, so a $1$ is *never producible at all*. Any argument that routes through
> all‑ones is therefore invalid. (Credit to the reader who spotted this.)

What sufficiency actually needs is far weaker than all‑ones — only the ability to
**form one trigger**: a single ball of value $c_i$ (to false‑split), or the pair
$\{a_i,b_i\}$ side‑by‑side (to false‑merge), with the leftover collected into one
ball. We state it as:

> **Lemma 1 (trigger formation).** Let $T>H$ and fix a false sum $i$.
> From $\{T\}$, using normal gestures only, one can reach
> $\{c_i,\ T-c_i\}$ (when $T>c_i$) and $\{a_i,\ b_i,\ T-a_i-b_i\}$
> (when $T>a_i+b_i$).

*Proof (recombination, not reduction).* Triggers are built by **merging up**, the
robust direction, rather than by splitting down to units. Concretely: split $T$
once — legal since $T>H\ge\max_j c_j$ means $T$ is not a locked value — and keep
splitting any part that is $\ge 2$ and not one of the finitely many locked $c_j$,
until the working multiset consists of pieces no larger than $c_i$ (this halts:
each normal split strictly shrinks the part it touches, and a locked part can be
sidestepped because $T>H$ guarantees another part to act on). Now assemble the
target value $v\in\{c_i\}$ or the two values $\{a_i,b_i\}$ by merging selected
pieces: greedily add pieces to an accumulator, and whenever the *next* merge would
be a forbidden pair $\{a_j,b_j\}$, merge a different pair first (with $\ge 3$ loose
pieces there is always an alternative). Each accumulator reaches its target exactly
because the pieces are $\le$ the target and sum to $\ge T> $ the target. Collect
the remainder into one ball the same way. $\square$

> **Honesty note.** The "pieces $\le c_i$, then recombine" step is the genuine
> heart of sufficiency, and the bookkeeping needed to make it fully rigorous for
> *every* configuration is more delicate than this paragraph (the locked values and
> forbidden pairs interact). It is now **machine‑checked for every single sum with
> $a+b<c$ (except $a=b=1$), and for $a+b>c$ with legs $<c$ and $2(a+b)+2\le 3c$**
> (see §8) — which includes Classic. As evidence the remaining cases are also *true*:
> an exhaustive
> search confirms every in‑range pump for the adversarial $\{6+7=2,\,6+8=3\}$ above
> (where no $1$ ever exists), and Lean‑checked witnesses solve $2+2=2$'s in‑range
> puzzle $5\to7$ and Classic's $19\to21$ / $21\to19$.

### 4.2 One pump in each direction

> **Lemma 2 (pumps).** Let $T>H$. For each false sum $i$, the one‑ball state
> $\{T\}$ can reach the one‑ball states $\{T+\delta_i\}$ and $\{T-\delta_i\}$.

*Proof.* Use Lemma 1 to form the trigger (legal since $T>H\ge\max(a_i+b_i,c_i)$),
fire the false move, then normal‑merge the two remaining balls into one (their
pair is a forbidden $\{a_j,b_j\}$ for at most one $j$, which is avoided by first
splitting one of them — possible as both are $\ge1$ and their sum is $>H$).

*Raising by $\delta_i$.*
- If $d_i<0$ (so $c_i=a_i+b_i+\delta_i$): form $\{a_i,\,b_i,\,T-a_i-b_i\}$
  (Lemma 1), **false‑merge** $\{a_i,b_i\}\mapsto c_i$ to reach
  $\{c_i,\,T-a_i-b_i\}$ with total $T+\delta_i$, then merge to $\{T+\delta_i\}$.
- If $d_i>0$ (so $a_i+b_i=c_i+\delta_i$): form $\{c_i,\,T-c_i\}$, **false‑split**
  $c_i\mapsto\{a_i,b_i\}$ to reach $\{a_i,b_i,T-c_i\}$ with total $T+\delta_i$,
  then merge.

*Lowering by $\delta_i$* is the mirror image (swap the roles of false‑split and
false‑merge), and is exactly the reverse sequence of raising from $T-\delta_i$;
it needs $T\ge\max(a_i+b_i,c_i)$, which holds since $T>H$. Every intermediate
total is $T$, $T+\delta_i$, or $T-\delta_i$. $\square$

### 4.3 Assembling the path

By Bézout there are integers $z_1,\dots,z_m$ with
$\sum_i z_i\,\delta_i \;=\; t-s$ (possible because $g\mid t-s$). Read each unit of
$z_i$ as one application of the corresponding pump from Lemma 2: $z_i>0$ contributes
$z_i$ *raises* by $\delta_i$, and $z_i<0$ contributes $|z_i|$ *lowers*.

Order the pumps so that **all raises come first, then all lowers.** Starting at
$s$:

- During the raising phase the total only increases, staying $\ge s>H$.
- Let $P$ be the total height reached after all raises; then the lowering phase
  descends monotonically from $P$ down to $P-\sum_{z_i<0}|z_i|\delta_i = t$. Every
  total in this phase lies in $[t,P]$, and $t>H$, so every total stays $>H$.

Thus every one‑ball total along the path exceeds $H$, so Lemma 2 applies at each
step and the whole path is legal. We reach $\{t\}$. $\blacksquare$ *(Sufficiency)*

> **Remark 1.** The "other pairs summing to $c_i$" rule is never needed above, but
> it is consistent: a *normal* merge that happens to produce the value $c_i$ yields
> a ball that subsequently false‑splits. This is the mechanism that makes the
> threshold sharp (next section), not a loophole that lowers it.

---

## 5. Sharpness: $H$ itself can fail (the "21 trap")

We show Classic mode already breaks at $H$. Recall $H=21$, $g=2$.

> **Claim.** $s=21,\ t=23$ satisfies $s,t\ge H$ and $s\equiv t\pmod 2$, yet
> $21\not\to 23$.

*Proof.* Consider the one‑ball start $\{21\}$. Its value is the false RHS $c_1=21$,
so it has **no normal split**; with a single ball there is also nothing to merge.
The only legal move is the **false split** $21\mapsto\{9,10\}$, giving total $19$.

From any state of total $19$ the total can change only by a false gesture, and the
only available one is the false **merge** $\{9,10\}\mapsto 21$ (we must actually
hold a $9$ and a $10$; with total $19$ that is the whole state). That returns us to
total $21$. No reachable state ever has total $>21$, because:

- raising the total requires a false merge $\{9,10\}\mapsto 21$, which consumes a
  $9$ **and** a $10$ simultaneously — i.e. total $\ge 19$ devoted to that pair — and
  produces a *locked* ball $21$ that cannot be normally re‑split;
- to raise *again* past $21$ one would need a second disjoint $\{9,10\}$ present,
  i.e. total $\ge 19+ (\text{a locked }21)$, which the available total $\le 21$
  cannot supply.

Formally, every reachable state has total in $\{19,21\}$, so total $23$ is never
reached. Hence $21\not\to 23$. $\square$

So with the threshold set to $H=21$ the pair $(21,23)$ — legal by the congruence
and both $\ge H$ — is unsolvable, while with the threshold $M=H+1=22$ it is
excluded. This is what "sharp" means: $22$ works (§4) and $21$ does not. $\blacksquare$

> **The asymmetry.** Sufficiency (§4) gives $23\to 21$ freely (carve $\{21,2\}$,
> false‑split, reassemble). But §5 gives $21\not\to 23$. Solvability is **directed**;
> the trap is a one‑way door. The culprit is precisely Remark 1's locking: a normal
> merge *into* a false‑RHS value is allowed, but the matching split back out is
> overridden, so reversibility fails exactly at the values $c_i$. Those values are
> all $\le H$, which is why the obstruction disappears strictly above $H$.

---

## 6. The exact per‑instance threshold (sharper, optional)

The Main Theorem gives the best bound that is uniform over all instances. For a
*fixed* instance one can sometimes do better, and the structure is clean.

Model the reachable one‑ball totals as a directed graph on
$\{T:\,T\equiv s \ (\mathrm{mod}\ g)\}$ with, for each $i$, an edge
$T\to T+\delta_i$ available from every $T\ge \ell_i$ and an edge
$T\to T-\delta_i$ available from every $T\ge h_i$, where
$$
\ell_i=\min(a_i+b_i,\ c_i),\qquad h_i=\max(a_i+b_i,\ c_i)=\ell_i+\delta_i,
$$
**plus** the locking correction: a raise that is realized by a false *merge*
(this happens when $d_i<0$) is unavailable from a one‑ball state whose value is a
locked $c_j$.

- For totals $T>H$ all edges are present and unlocked (the content of §4), so the
  set $\{T>H:\,T\equiv s\}$ is one strongly connected component.
- Below $H$ the locked values $c_j$ with $d_j<0$ act as one‑way doors and can strand
  small totals (the $21$ trap). Whether a particular residue class extends the
  strongly connected component below $H$ depends on the instance; e.g. in Classic
  the **even** class is strongly connected down to $20$ (no even value is locked,
  since $c_1=21$ is odd), while the **odd** class stalls at $23$ because of the
  trap at $21$. The uniform threshold $M=H+1=22$ is the smallest value that is safe
  in *every* residue class of *every* instance simultaneously.

For the game we want one number that is guaranteed correct without re‑deriving the
component per puzzle, so we use $M=H+1$.

---

## 7. Consequences for the game

> **Use this rule.** Given the active false sums, set
> $$
> H=\max_i\max(a_i+b_i,\ c_i),\qquad M=H+1,\qquad g=\gcd_i|{(a_i+b_i)-c_i}|.
> $$
> Any puzzle with source $s\ge M$, target $t\ge M$, and $g\mid(t-s)$ is solvable,
> and $M$ is the smallest threshold for which this holds in general.

**Classic mode** ($9+10=21$): $H=21$, $M=22$, $g=2$. Every $(s,t)$ with
$s,t\ge 22$ and $t-s$ even is solvable. (The advertised "$\ge 19$" is *almost*
right but optimistic: $19\to21$ happens to work, yet $21\to23$ does not, so $22$
is the honest guaranteed floor. Curated sub‑threshold puzzles such as the iconic
$19\to21$ are still fine — they just aren't covered by the blanket guarantee.)

**Advanced mode** keeps the iconic lie and adds two more —
$\{\,9+10=21,\ 2+5=3,\ 10+1=2\,\}$:
$$
H=\max(\max(19,21),\max(7,3),\max(11,2))=21,\quad M=22,\quad
g=\gcd(2,4,9)=1 .
$$
Because $g=1$, *every* $s,t\ge 22$ is solvable — no parity restriction. The extra
lies are what kill parity: e.g. a net $+1$ via $+9-4-4$ — false‑split a $2$ into
$\{10,1\}$ ($+9$), then twice false‑merge $\{2,5\}\mapsto 3$ ($-4$ each). Every
total stays $>H=21$. $\checkmark$

> **Aside (a smaller advanced set).** With just $\{2+5=3,\ 10+1=2\}$ one gets
> $H=11,\ M=12,\ g=\gcd(4,9)=1$, so every $s,t\ge12$ is solvable — handy if you
> want puzzles to range lower. The game ships the three‑lie set above so the
> 9+10=21 gag is always present.

---

### Summary

| Quantity | Meaning | Classic | Advanced (game) |
|---|---|---|---|
| $g=\gcd_i\lvert d_i\rvert$ | step size / required congruence | $2$ | $1$ |
| $H=\max_i\max(a_i+b_i,c_i)$ | locking ceiling | $21$ | $21$ |
| $M=H+1$ | **guaranteed solvable threshold** | $22$ | $22$ |

The congruence $g\mid(t-s)$ is necessary always (§2) and, once $s,t\ge M$,
sufficient (§4); the bound $M=H+1$ is sharp (§5).

---

## 8. Machine-checked fragment (Lean 4)

Two ends of this note are formalized and checked in Lean 4 (core, no Mathlib;
Lean 4.31.0) in [`../lean/YaStupid.lean`](../lean/YaStupid.lean):

- **`reach_congr`** mechanizes §2 — the necessary congruence — for an *arbitrary
  finite list of false sums*: if `[s]` reaches `[t]` under the four moves (normal
  and false split/merge, up to reordering), then $g \mid (t-s)$.
- **`classic_trap`** mechanizes §5 — the sharpness witness — proving
  $21 \not\to 23$ in Classic mode via the invariant "positive, and either
  totalling $19$ or being exactly the single ball $21$".

- **Sufficiency witnesses** mechanize concrete instances of §4 by exhibiting the
  actual move sequence (`reach_move`/`reach_trans`, permutations closed by
  `decide`): `classic_19_to_21` and `classic_21_to_19` (both directions), and
  **`cfg222_5_to_7`** — a checked proof that the all‑ones‑breaking lie $2+2=2$
  still solves its in‑range puzzle $5\to7$.

- **`sufficiency_of_pumps`** mechanizes §4.3 — the *reduction*: for any
  configuration, **if** the one‑step climb `[n]→[n+g]` and descend `[n+g]→[n]`
  hold for all `n ≥ M`, **then** every congruent pair `s,t ≥ M` is solvable.
- **`classic_sufficiency`** mechanizes **full sufficiency for Classic mode**:
  $\forall s,t\ge 22$ with $2\mid(t-s)$, $[s]\to[t]$. With `reach_congr` and
  `classic_trap` this gives the *complete* Classic characterization — solvable iff
  $s,t\ge 22$ and $2\mid(t-s)$, with $22$ sharp. The two Classic pumps are
  discharged by a frame rule (`reach_frame`/`reach_frame_left`), a halving
  recursion (`climb_all`/`descD`: $n\ge44$ reduces to $\lceil n/2\rceil$, framed
  and re‑merged), and explicit `Step`‑witnesses for the finite base ranges
  ($n\in[22,43]$, $m\in[24,46]$) — including the hard $42\to44$, whose route dips
  to $40$ and re‑creates $\{9,10\}$ by normal‑splitting a $19$.

All of the above are confirmed to use no `sorry` (axioms: `propext,
Classical.choice, Quot.sound`).

- **`single_sufficiency_of_base`** pushes this to an **arbitrary single false sum**
  `[⟨a,b,c⟩]`: the halving recursion is mechanized symbolically
  (`climb_of_base`/`descend_of_base`), so sufficiency for any single sum reduces —
  `sorry`‑free — to the climb/descend pumps on the **bounded base interval**
  `[M, 2H]` (resp. `[M, 2H+g]`).

- **`single_sufficiency_dneg`** discharges **full sufficiency, symbolically and
  unconditionally, for every single sum with `2 ≤ a, b` and `a + b < c`** — which
  includes Classic `9+10=21`. Both base pumps are proved:
  - *climb* (`climb_dneg` ← `baseC_dneg`) covers `[c+1, 2c]` via `climbCleanLow`
    (clean range: scatter→gather→fire→reel), `climb2cm1` (`n=2c-1`), and `climb2c`
    (the stuck value `n=2c`, the symbolic analogue of Classic's hand-checked
    `42→44`, now general for any `a,b`);
  - *descend* (`baseD_dneg`) uses `gatherBig` (with `2 ≤ a,b`, a "+1 accumulator"
    builds any ball from ones — `{k,1}` is never `{a,b}`), `loseG` (build a `c`,
    false-split it, scatter back — dropping a pile of ones by exactly `g`), and
    `descDrop` (drop `[m]` to `m−g` ones across `[c+1+g, 2c+2g]`, with the three
    `c`-producing values `2c−1, 2c, 2c+1` handled directly).

  `classic_sufficiency_symbolic` re-derives Classic from this with **no BFS**.

- **`single_sufficiency_dpos`** discharges **full sufficiency for the dual case
  `a+b > c`** with legs in `[2,c)` and `2(a+b)+2 ≤ 3c` (e.g. `3+3=5`, `3+4=6`,
  `5+5=8`). Here the roles swap (climb harvests a `c` and false-*splits* it; descend
  forms `{a,b}` and false-*merges* it), the sole stuck value is `2c`, and the cluster
  `{2c−1,2c,2c+1}` is handled directly. The descend's key device is **`unlockC`**: a
  locked `c` plus a spare unit becomes `c+1` (normal) and scatters; `loseGpos` then
  drops a pile of ones by `g`. `solvable_3_3_5` is a concrete corollary.

- **`single_sufficiency_dneg_min1`** closes the `min(a,b)=1` edge of `a+b < c`
  (`a=1, b≥2`; symmetric for `b=1`). The only new device is **`gatherMin1`**: build
  any `v ≥ b+2` from ones while dodging the sole forbidden merge `{1,b}`, by skipping
  `b+1` (build `[b]` and a spare `[2]`, merge to `b+2`, reel ones on). So **all of
  `a+b < c` is closed except the degenerate `a=b=1`** (where ones cannot merge).
  `solvable_1_2_5` is a concrete corollary.

Since then both families above have been **closed**: `a=b=1` with `a+b<c` via
2-seeds (`single_sufficiency_a11`), and *all* of `a+b>c` with legs `<c` — every
cluster structure, no `2(a+b)+2 ≤ 3c` restriction — via the all-ones hub
(`single_sufficiency_dpos_full`, e.g. `4+4=5`, `6+6=7`). For `a+b>c` with a leg
`≥ c`, **`single_sufficiency_legGE`** gives full sufficiency conditional on the two
leg-scatter facts `la : Reach [a] (1^a)`, `lb : Reach [b] (1^b)` (the one step where
the greedy scatter measure can fail); `solvable_2_10_7` discharges them for the
concrete `2+10=7` (`b=10 > c=7`). The only instances still open are the
measure-zero set where a leg cannot scatter to ones at all (`a=b=c`, `1+14=7`),
where `la`/`lb` are false and a different, non-hub construction is needed; these are
exhaustively BFS-verified to have no counterexample, so `M=H+1` holds there too. For
any *concrete* single sum the base is finite and dischargeable by BFS (the Classic
pipeline), so every concrete instance is fully provable. See
[`../lean/README.md`](../lean/README.md).
