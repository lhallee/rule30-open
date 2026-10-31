---
title: A random right half driven by a period-four word, the exact law of its row and a zero-one reduction of entry
category: columns
problems: [1]
status: paper
formalization: wanted
---

# A random right half driven by a period-four word, the exact law of its row and a zero-one reduction of entry

Let a right half be a sequence of fair coins and drive it by a word $w$ of period four in column 0, as in the kit's
`drv`. Then:

- **(A) The law of the row.** One driven step is injective on a set of full measure, and it maps the fair-coin measure
  $\mu$ to $2 \cdot \mathbb{1}_{E} \cdot \mu$, where $E$ is its image, a compact set of measure $1/2$. So the row at
  time $t$ is uniform on a compact set $E_t$ of measure exactly $2^{-t}$. Its columns beyond $t$ are fair coins that do
  not depend on the drive and evolve by the undriven step; its columns 1 to $t$ are a function of them almost surely.
  Distinct halves in one set of full measure stay distinct at every time.
- **(B) A zero-one reduction.** Let $N_\varphi$ be the set of halves that never enter the kit's ether-and-wall family
  at drive phase $\varphi$. Then $\mu(N_\varphi) = 0$ if and only if a half that starts with any given finite prefix
  enters with probability 1, if and only if these conditional probabilities have a positive lower bound over all
  prefixes. Running the dynamics forward only reproduces the question: $N_{\varphi + t}$ has density
  $\mu(N_\varphi)$ in $E_t$.
- **(C) A tail bound for $0001$.** With $\tau$ the time of entry, $P(\tau > T) \ge 2^{-(T + 20)}$ at every drive phase,
  from halves that start with a long piece of the [background of 80 cells](background-halves.md). So no bound
  $P(\tau > T) \le C \rho^T$ holds with $\rho < 1/2$.
- **(D) Column 1.** The one-cell constraint $z_s = 1 \Rightarrow z_{s+1} = \lnot c_s$ gives crude upper bounds on the
  growth of the words column 1 can read under the drive: $0.521$, $0.565$ and $0.656$ bits per step for $0001$, $0011$
  and $0111$. For $0001$ the block graph of [column-one blocks](column-one-blocks.md) (A) gives the sharper bound
  $0.307$ bits per step.

Whether $\mu(N_\varphi) = 0$, that is, whether almost every infinite right half enters the family, is open. The
argument below says where it stops.

## Setting

Write $X = \{0, 1\}^{\{1, 2, \dots\}}$ for right halves and $X' = \{0, 1\}^{\{0, 1, \dots\}}$, each with the fair-coin
product measure, $\mu$ on $X$ and $\mu'$ on $X'$. Rule 30 is $r(a, b, c) = a \oplus (b \lor c)$. The undriven step is
$G : X' \to X$,

$$G(x)_j = x_{j-1} \oplus (x_j \lor x_{j+1}) \qquad (j \ge 1),$$

and the step driven by a center value $c$ is $F_c : X \to X$, $F_c(x) = G(c x)$, where $c x \in X'$ puts $c$ at cell 0.
This is the kit's `drv`: column 0 at time $t$ is $c_t$, and the row at time $t + 1$ is $F_{c_t}$ of the row at time
$t$. For a word $w$ of period four and a phase $\varphi$, the drive is $c_t = w[(t + \varphi) \bmod 4]$, the row is
$R_t = \Phi_t(x)$ with $\Phi_t = F_{c_{t-1}} \circ \dots \circ F_{c_0}$, and $E_t = \Phi_t(X)$.

A half $x$ **enters** at phase $\varphi$ when, for one of the kit's alignments $(j_0, s)$ of $w$ (`A0001`, `A0011`,
`A0111`) and some $t_1$, the driven half is in the family at time $t_1$: `InFamily (drv c x) j0 (s + φ) t1`, exactly
the conclusion of the kit's `Absorption`. That is, for some $k$ with $j_0 + k \equiv 2 \pmod 7$, columns 1 to $k$ of
$R_{t_1}$ are the ether and columns $k + 1$ to $k + 13$ are a wall state. Let $\mathcal{A}_\varphi \subseteq X$ be the
halves that enter, $N_\varphi = X \setminus \mathcal{A}_\varphi$, and $\tau(x)$ the least such $t_1$. All of these
depend on $\varphi$ only modulo 4.

## Proof

### The undriven step

These three facts are the kit's two-sided results, proved for the one-sided map $G$ by the same local arguments.

1. **$G$ maps $\mu'$ to $\mu$.** A cylinder $[y_1 \dots y_n]$ of $X$ has exactly 4 preimage words $x_0 \dots x_{n+1}$:
   choose $x_n$ and $x_{n+1}$ freely, then $x_{j-1} = y_j \oplus (x_j \lor x_{j+1})$ for $j = n, \dots, 1$ fixes the
   rest, because Rule 30 is permutive in its left cell. So $\mu'(G^{-1}[y]) = 4 \cdot 2^{-(n+2)} = 2^{-n} = \mu([y])$,
   and cylinders determine the measure. The kit proves this for two-sided Rule 30 (`Mixing.measurePreserving_evol`).
2. **The word $010$ pins its left neighbor.** If $G(x)$ reads $0, 1, 0$ at cells $j, j + 1, j + 2$, then $x_{j-1} = 1$.
   Were $x_{j-1} = 0$, then $G(x)_j = x_j \lor x_{j+1} = 0$ would make $x_j = x_{j+1} = 0$, then $G(x)_{j+1} =
   x_{j+2} = 1$, and then $G(x)_{j+2} = 0 \oplus (1 \lor x_{j+3}) = 1$, a contradiction. Since $x_{j-1} = 1$,
   $x_{j-2} = y_{j-1} \oplus 1$ whatever $x_j$ is, and then the leftward recursion of step 1 fixes $x_{j-3}, \dots,
   x_0$ from $y_1, \dots, y_{j-2}$, so any two preimages of $y$ agree on cells $0$ to $j - 1$. This is the kit's `Preimages.eq_true_of_window` and
   `Preimages.eq_of_evol_one_eq_of_window`.
3. **Unique preimages almost surely.** Let $Y \subseteq X$ be the rows that read $010$ at infinitely many positions.
   The disjoint blocks of cells $3m + 1, 3m + 2, 3m + 3$ are independent and each reads $010$ with probability $1/8$,
   so $\mu(Y) = 1$. By step 2, two preimages of a row in $Y$ agree on arbitrarily long prefixes, so every row in $Y$
   has at most one preimage, and by step 1, $\mu'(G^{-1} Y) = 1$. This is the kit's
   `Preimages.eq_of_evol_one_eq_of_frequently` and `Mixing.ae_existsUnique_preimage`.

### (A) The law of the driven row

**One step.** Fix $c$ and let $C = \{x' \in X' : x'_0 = c\}$. The map $x \mapsto c x$ carries $\mu$ to
$2 \mu'$ restricted to $C$. Let $E = F_c(X) = G(C)$, a compact set as the continuous image of a compact one.

- *$G^{-1}(E \cap Y) = C \cap G^{-1}(Y)$.* If $x' \in C$ and $G(x') \in Y$, then $G(x') \in E \cap Y$. Conversely, if
  $G(x') \in E \cap Y$, then $G(x') = G(x'')$ for some $x'' \in C$, and the unique preimage gives $x' = x'' \in C$. The
  same argument gives $G^{-1}(B \cap E \cap Y) = C \cap G^{-1}(B) \cap G^{-1}(Y)$ for every Borel set $B$.
- *The measure of $E$.* $\mu(E) = \mu(E \cap Y) = \mu'(G^{-1}(E \cap Y)) = \mu'(C \cap G^{-1} Y) = 1/2$.
- *The pushforward.* For Borel $B \subseteq X$,
  $$\mu(F_c^{-1} B) = 2\, \mu'(C \cap G^{-1} B) = 2\, \mu'(G^{-1}(B \cap E \cap Y)) = 2\, \mu(B \cap E \cap Y) = 2\, \mu(B \cap E).$$
  So $(F_c)_* \mu = 2 \cdot \mathbb{1}_E \cdot \mu$.
- *Injectivity.* If $F_c(x) = F_c(x'') \in Y$, then $G(c x) = G(c x'') \in Y$, so $c x = c x''$. Hence $F_c$ is
  injective on $S = F_c^{-1}(Y)$, and $\mu(S) = 2 \mu(Y \cap E) = 1$.

**Many steps.** Suppose $(\Phi_t)_* \mu = 2^t \cdot \mathbb{1}_{E_t} \cdot \mu$, and let $F = F_{c_t}$ with $S =
F^{-1}(Y)$ and image $E$. Then $E_t \cap S = F^{-1}(E_{t+1} \cap Y)$: one inclusion is clear, and if $F(x) \in E_{t+1}
\cap Y$, then $F(x) = F(x'')$ with $x'' \in E_t$, both in $S$, so $x = x'' \in E_t$. Since $S$ has full measure and
$E_{t+1} \subseteq E$,

$$\mu(E_t \cap F^{-1} B) = \mu(F^{-1}(E_{t+1} \cap Y \cap B)) = 2\, \mu(E_{t+1} \cap B),$$

so $\mu(\Phi_{t+1}^{-1} B) = 2^t \mu(E_t \cap F^{-1} B) = 2^{t+1} \mu(E_{t+1} \cap B)$. With $B = X$, $\mu(E_{t+1}) =
2^{-(t+1)}$. By induction, **$R_t$ has law $2^t \cdot \mathbb{1}_{E_t} \cdot \mu$, the uniform measure on the compact
set $E_t$, and $\mu(E_t) = 2^{-t}$.**

**The far part.** For $j \ge 2$, $F_c(x)_j = x_{j-1} \oplus (x_j \lor x_{j+1})$ does not involve $c$. Let $\omega_t \in
X'$ be the columns beyond $t$, $(\omega_t)_i = (R_t)_{t+1+i}$. Then $(\omega_{t+1})_i = G(\omega_t)_{i+1}$: the far
part evolves by the undriven step, with no drive, starting from $x$ itself. By steps 1 and 3 each such step preserves
the fair-coin measure and is injective on a set of full measure. So $\omega_t$ is a sequence of fair coins, $x$ is an
almost-sure function of $\omega_t$ (a Borel one by the Lusin–Souslin theorem, as in the kit's `Invertibility`), and so
are columns 1 to $t$ of $R_t$: $(R_t)_{1..t} = \Psi_t(\omega_t)$ almost surely. The drive enters only through
$\Psi_t$.

**Distinct halves stay distinct.** Let $S_\infty = \bigcap_{s \ge 1} \Phi_s^{-1}(Y)$, of full measure because
$\mu(\Phi_s^{-1}(X \setminus Y)) = 2^s \mu(E_s \setminus Y) = 0$. If $x \ne x''$ in $S_\infty$ had $\Phi_t(x) =
\Phi_t(x'')$ with $t$ least, then $F_{c_{t-1}}$ would identify the distinct halves $\Phi_{t-1}(x)$ and
$\Phi_{t-1}(x'')$ at a row in $Y$, against injectivity. This excludes only exact equality of whole halves. It says
nothing about agreement on a window near column 0, which is what [the synchronization
question](../../negative-results/dynamics/synchronization.md) asks; for two-sided Rule 30 the kit shows that distinct
configurations can agree on a window forever (`Preimages.not_positivelyExpansive`).

### (B) The zero-one reduction

- *$N_\varphi$ is closed.* Membership in the family at time $t_1$ with depth $k$ reads columns 1 to $k + 13$ of
  $R_{t_1}$, which depend on cells 1 to $k + 13 + t_1$ of $x$. So $\mathcal{A}_\varphi$ is a countable union of
  cylinders, open, and $N_\varphi$ is closed, as [the background halves](background-halves.md) already notes.
- *$N_\varphi = F_{c_0}^{-1}(N_{\varphi + 1})$.* The half driven from phase $\varphi$ at time $t + 1$ is the half
  $F_{c_0}(x)$ driven from phase $\varphi + 1$ at time $t$, with the same ether phase, so $x$ is in the family at time
  $t_1 + 1$ exactly when $F_{c_0}(x)$ is at time $t_1$. A half in the family at time 0 is also in it at time 1 by the
  kit's `trap_invariant` (column 0 is the ether column $j_0$ because the alignment is one of the kit's). So $x$ enters
  if and only if $F_{c_0}(x)$ does.
- *The density.* Iterating, $N_\varphi = \Phi_t^{-1}(N_{\varphi + t})$, and by (A), $\mu(N_\varphi) = 2^t \mu(N_{\varphi
  + t} \cap E_t)$, that is, $\mu(N_{\varphi + t} \cap E_t) / \mu(E_t) = \mu(N_\varphi)$ for every $t$.
- *Zero-one.* If $\mu(N_\varphi) = 0$, then $\mu(\mathcal{A}_\varphi \mid [p]) = 1$ for every prefix $p$, since cylinders
  have positive measure, and the infimum over $p$ is 1. If $\mu(N_\varphi) > 0$, Lévy's upward theorem gives
  $\mu(N_\varphi \mid [x_1 \dots x_n]) \to \mathbb{1}_{N_\varphi}(x)$ for almost every $x$, so at some $x \in
  N_\varphi$ the conditional probabilities $\mu(\mathcal{A}_\varphi \mid [x_1 \dots x_n])$ tend to 0 and their
  infimum is 0. Hence the three conditions of (B) are equivalent. This is a standard fact about any measurable set
  under a product measure with positive cylinders.
- *Density of entering halves.* $\mu(N_\varphi) = 0$ implies that every finite prefix extends to a half that enters.
  So does the kit's `Absorption`, since the prefix followed by white cells is a finite half. No implication between
  $\mu(N_\varphi) = 0$ and `Absorption` is known in either direction.

### (C) The tail bound for $0001$

Take $w = 0001$ and a phase $\varphi$. The [background of 80 cells](background-halves.md) has a column $x_0$ that reads
$0001$ from phase $ph_0$, and the kit's driven half from it is the background itself
([BackgroundHalves](../../Rule30Open/Columns/BackgroundHalves.md), `drv_eq`): with $b$ the background to the right of
column $x_0$ at phase $ph_0 + \varphi$, the half $b$ driven from phase $\varphi$ reads `Fb x0 ph0 (φ + t)` at time $t$,
by the induction of `drv_eq` with `colOK_spec h (t + φ)`, since the column repeats $0001$. `drv_eq` itself is stated
for drive phase 0 only; the phase-$\varphi$ version is not a separate Lean theorem. So every drive phase is realized.

Let $x$ agree with $b$ on cells 1 to $T + 20$. Column $p$ at time $t$ depends on the drive and on cells 1 to $p + t$,
so for $t \le T$, $R_t(x)$ and $R_t(b)$ agree on columns 1 to 20. Suppose $R_t(x)$ is in the family at depth $k$ for
some alignment.

- If $k \ge 8$, then $R_t(x)$, and with it $R_t(b)$, carries the ether on columns 1 to 8. `prefix_short` at time
  $(\varphi + t) \bmod 8$, with `Fb_period` for all times, excludes this for every alignment $j < 7$, $s < 4$ of the
  ether.
- If $k \le 7$, then membership reads columns 1 to $k + 13 \le 20$, so $R_t(b)$ is in the family at time $t$, which
  `not_inFamily` excludes for all $j_0$, $s$ and times.

So $\tau(x) > T$, and $P(\tau > T) \ge \mu([b_1 \dots b_{T+20}]) = 2^{-(T + 20)}$. If $P(\tau > T) \le C \rho^T$ for all
$T$, then $2^{-(T+20)} \le C \rho^T$, so $\rho \ge 1/2$. The bound comes from one cylinder and is weak: it says nothing
about $\mu(N_\varphi)$.

### (D) Column 1

Column 1 obeys $z_{s+1} = c_s \oplus (z_s \lor (R_s)_2)$, so $z_s = 1$ forces $z_{s+1} = \lnot c_s$, while $z_s = 0$
leaves $z_{s+1}$ free. With states $z_s \in \{0, 1\}$, the transfer matrices are $M_0 = \begin{pmatrix} 1 & 1 \\ 0 & 1
\end{pmatrix}$ and $M_1 = \begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$, and the number of words that satisfy the
constraint over $4m$ steps grows like $\lambda^m$, with $\lambda$ the largest eigenvalue of the product over one
period (the same for every phase):

| Word | Product | $\lambda$ | Bits per step, $\tfrac14 \log_2 \lambda$ |
|---|---|---|---|
| $0001$ | $M_0^3 M_1 = \begin{pmatrix} 4 & 1 \\ 1 & 0 \end{pmatrix}$ | $2 + \sqrt5$ | $0.521$ |
| $0011$ | $M_0^2 M_1^2 = \begin{pmatrix} 4 & 3 \\ 1 & 1 \end{pmatrix}$ | $(5 + \sqrt{21})/2$ | $0.565$ |
| $0111$ | $M_0 M_1^3 = \begin{pmatrix} 5 & 3 \\ 2 & 1 \end{pmatrix}$ | $3 + \sqrt{10}$ | $0.656$ |

These are crude upper bounds: they use only the one-cell constraint and ignore $(R_s)_2$. For $0001$ the repository
already has a sharper one. By [column-one blocks](column-one-blocks.md) (A), column 1 beside $0001$ follows the
13-edge block graph $0 \to \{1, 2, 3, 4\}$, $1 \to \{2, 3, 4\}$, $2 \to \{1, 2\}$, $3 \to \{2, 3\}$, $4 \to \{0, 1\}$,
whose spectral radius is $2.3402$, so column 1 grows by at most $\tfrac14 \log_2 2.3402 = 0.307$ bits per step, against
$0.521$ from the table.

This bounds column 1 only. It says nothing about columns 17, 15 and 14, where the universal sequences of
[LockWord](../../Rule30Open/Columns/LockWord.md) for $0001$, $0011$ and $0111$ would have to appear.

## What it means

- **For the route to least period four.** The route needs every finite right half to enter the family (`Absorption`).
  $\mu(N_\varphi) = 0$ is a different statement, about infinite halves, and no implication between the two is known
  in either direction. (B) turns the measure statement into a uniform one: a
  $\delta > 0$ with $\mu(\mathcal{A}_\varphi \mid [p]) \ge \delta$ for every prefix $p$. The [census](absorption-census.md)
  is consistent with it: 2,000 random infinite halves per word and phase all enter.
- **What the randomness buys.** By (A), a random half stays random in the only part the drive cannot see: beyond
  column $t$ the row is fair coins evolving by undriven Rule 30, and each step of the drive costs exactly one bit, the
  measure of $E_t$ halving. The drive acts only through $\Psi_t$; entry at time $t$ depends on $\omega_t$ and
  $\Psi_t(\omega_t)$.
- **For $0001$.** The tail of $\tau$ is at least exponential with base $1/2$, because a half can copy the background of
  80 cells, which never enters, for as long as it likes.

## Where it stops

By (B), $\mu(N_\varphi) = 0$ needs a $\delta > 0$ with $\mu(\mathcal{A}_\varphi \mid [p]) \ge \delta$ for every prefix
$p$. By (A), the drive acts only through $\Psi_t$, and entry at time $t$ depends on $\omega_t$ and
$\Psi_t(\omega_t)$; nothing is known about how $\Psi_t$ depends on $\omega_t$.

- **The hard prefixes.** Fix the end phase by taking $t \equiv 0 \pmod 4$, and let $K_\varphi = N_\varphi \cap
  \bigcap_{m \ge 0} E_{4m}$, the halves that never enter and have a driven past of every length. $K_\varphi$ contains
  the aligned ether halves, which never enter ([the census](absorption-census.md)), and the halves of the
  [background of 80 cells](background-halves.md) for $0001$, which repeat with period 8. These are the only known
  points of $N_\varphi$; their prefixes are natural test cases for $\delta$, but a failure of uniform $\delta$ need not
  occur near $K_\varphi$, which has measure zero by (A).
- **What a proof would need there (heuristic).** Near a background half, the random tail has to erode the background
  and then let the half enter; the entry times of truncations suggest erosion at about $2/5$ of a column per step
  ([background halves](background-halves.md), measured, not proved). Near the aligned ether, which the drive reproduces exactly
  with period 4 and which is in the family at none of its phases, entry has to come from a wall forming to the right of an ether prefix. A uniform
  bound needs an "erode or build a wall" dichotomy for the leftward propagation of a random tail through the OR of Rule
  30, near every point of $K_\varphi$ at least. None is proved, for any infinite family of random continuations.
- **(A) alone is circular.** The density of $N_{\varphi + t}$ in $E_t$ equals $\mu(N_\varphi)$ for every $t$, so
  following the law of the row forward gives back the unknown.
- **Prefixes.** $\mu(N_\varphi) = 0$ would imply that every prefix extends to a half that enters; this is open in
  general and known only for the prefixes the computations and Lean results of the route cover.

## In the kit

The kit proves the undriven facts for two-sided Rule 30 in its equivalent forms:
[`Preimages`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/Preimages.lean)
(`eq_true_of_window`, `eq_of_evol_one_eq_of_window`, `eq_of_evol_one_eq_of_frequently`),
[`Mixing`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/Mixing.lean)
(`measurePreserving_evol`, `ae_existsUnique_preimage`, `exists_injOn_ae`, `ae_injective_iterate`) and
[`Invertibility`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/Invertibility.lean)
(a measure-preserving inverse almost everywhere). Steps 1 to 3 restate them for the one-sided map. The kit's
[`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)
defines `drv`, `InFamily`, `trap_invariant` and `Absorption`, which is about finitely supported halves only. Not in
the kit or this repository: the driven pushforward $(F_c)_* \mu = 2 \cdot \mathbb{1}_E \cdot \mu$ and the law of $R_t$
that follows from it, the tail bound (C), which uses `prefix_short`, `wall_absent` and `not_inFamily` of
[BackgroundHalves](../../Rule30Open/Columns/BackgroundHalves.md), and the column-1 bounds (D) for $0011$ and $0111$.
For $0001$, [column-one blocks](column-one-blocks.md) (A) already bounds column 1 more sharply than (D). The zero-one
reduction (B) is standard measure theory applied to the kit's family.

## Checks

The results above are paper proofs, and no computation in this repository checks them. The transfer matrix products
and eigenvalues of (D), and the spectral radius $2.3402$ of the block graph of [column-one
blocks](column-one-blocks.md), are small enough to check by hand or with any eigenvalue routine.
