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

### 4.1 A partition lemma

> **Lemma 1 (carving).** Let $T>H$. From the one‑ball state $\{T\}$ one can reach,
> using only normal gestures, any two‑part state $\{v,\,T-v\}$ with $1\le v\le T-1$,
> and more generally the three‑part state $\{a,\,b,\,T-a-b\}$ whenever
> $a,b\ge 1$ and $a+b\le T-1$.

*Proof.* First, $\{T\}$ can reach the all‑ones state $\{1,1,\dots,1\}$: repeatedly
split the smallest part that exceeds $1$. Each split strictly decreases the part
it acts on, so the process terminates with every part equal to $1$. The only
values that *cannot* be split are the finitely many $c_j\le H$; whenever the
chosen smallest part equals some $c_j$, the state has total $T>H\ge c_j$ and
therefore contains another part, which we split instead (or we first merge two
parts to move off the value $c_j$). Once at all‑ones, group the units by normal
merges into blocks of sizes $a$, $b$, and $T-a-b$. A merge is blocked only for
the finitely many forbidden pairs $\{a_j,b_j\}$; if assembling a block would force
such a pair, build the block in a different order (add a third unit first), which
is always possible because each block we build has size $\ge 1$ and we have units
to spare. $\square$

The two‑part claim is the case where one of the three blocks is empty.

### 4.2 One pump in each direction

> **Lemma 2 (pumps).** Let $T>H$. For each false sum $i$, the one‑ball state
> $\{T\}$ can reach the one‑ball states $\{T+\delta_i\}$ and $\{T-\delta_i\}$, and
> every intermediate state used has total in $\{T,\,T\pm\delta_i\}\subseteq(H-\delta_i,\infty)$.

*Proof.* Two cases by the sign of $d_i$; in both, $T>H\ge\max(a_i+b_i,c_i)$, so
all the carvings below are legal by Lemma 1, and **no ball we ever hold equals
any $c_j$ unless we put it there on purpose**, because every value in play is
$>H\ge\max_j c_j$ except the deliberately created $c_i$.

*Raising by $\delta_i$.*
- If $d_i<0$ (so $c_i=a_i+b_i+\delta_i$): carve $\{a_i,\,b_i,\,T-a_i-b_i\}$
  (Lemma 1), **false‑merge** $\{a_i,b_i\}\mapsto c_i$ to reach
  $\{c_i,\,T-a_i-b_i\}$ with total $T+\delta_i$, then normal‑merge to
  $\{T+\delta_i\}$.
- If $d_i>0$ (so $a_i+b_i=c_i+\delta_i$): carve $\{c_i,\,T-c_i\}$, **false‑split**
  $c_i\mapsto\{a_i,b_i\}$ to reach $\{a_i,b_i,T-c_i\}$ with total $T+\delta_i$,
  then normal‑merge.

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

**Advanced mode**, example $\{2+5=3,\ 10+1=2\}$:
$$
H=\max(\max(7,3),\ \max(11,2))=11,\quad M=12,\quad g=\gcd(4,9)=1 .
$$
Because $g=1$, *every* $s,t\ge 12$ is solvable — no parity restriction. A sample
solution $12\to13$ (net $+1=+9-4-4$): from $12$ false‑split a $2$ into $\{10,1\}$
($+9\Rightarrow 21$), then twice false‑merge $\{2,5\}\mapsto 3$
($-4\Rightarrow 17\Rightarrow 13$). Every total stays $>H=11$. $\checkmark$

---

### Summary

| Quantity | Meaning | Classic | Example Advanced |
|---|---|---|---|
| $g=\gcd_i\lvert d_i\rvert$ | step size / required congruence | $2$ | $1$ |
| $H=\max_i\max(a_i+b_i,c_i)$ | locking ceiling | $21$ | $11$ |
| $M=H+1$ | **guaranteed solvable threshold** | $22$ | $12$ |

The congruence $g\mid(t-s)$ is necessary always (§2) and, once $s,t\ge M$,
sufficient (§4); the bound $M=H+1$ is sharp (§5).
