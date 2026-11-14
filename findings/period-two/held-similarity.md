---
title: H^n is a bijective 2-adic similarity of ratio 2^n on each class modulo 2^n, as the 3x+1 map is, but affine on no residue class, so K is the attractor of two nonaffine similarities and the cycle equation and Bernstein's series have no closed form here
category: period-two
problems: [1]
status: paper
formalization: partial
evidence: [computations/held_similarity.py]
---

# H^n is a bijective 2-adic similarity of ratio 2^n on each class modulo 2^n, as the 3x+1 map is, but affine on no residue class, so K is the attractor of two nonaffine similarities and the cycle equation and Bernstein's series have no closed form here

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map of
[HeldColumn](../../Rule30Open/PeriodTwo/HeldColumn.md) on the 2-adic integers (bit $j$ is cell $j$), $c_t(U)$ bit 0 of
$H^t(U)$, and $K$ the set of $U$ with $c_t(U) = 1$ at every odd $t$ ([the shift model](shift-model.md)). Write
$|x|_2 = 2^{-v(x)}$. The 3x+1 map $T$ has three properties on which the 2-adic theory of the Collatz problem rests
(Lagarias 1985; Bernstein 1994; Bernstein and Lagarias 1996): the parity-vector map is an isometry conjugating $T$ to
the shift, $T^n$ is a bijective affine map from each class modulo $2^n$ onto $\mathbb Z_2$, and the inverse branches
$x \mapsto 2x$, $x \mapsto (2x - 1)/3$ are affine, which gives each periodic parity word a rational by the cycle equation
and the inverse conjugacy as an explicit series. This entry proves that $H$ has the first property and the first half
of the second, exactly, and that the affinity fails on every class for every iterate.

## Result

1. **The column map is an isometric conjugacy to the shift** (paper; the bijection is
   `column_bijective` of [ShiftModel](../../Rule30Open/PeriodTwo/ShiftModel.md), and the kit has it in its encoding as
   `Rule30ZeroBoundary.realization` with `zrow_aff`). Let $Q(U) = \sum_t c_t(U) 2^t$. Then $Q$ is a bijective isometry
   of $\mathbb Z_2$, $Q \circ H = \sigma \circ Q$ for the shift $\sigma(x) = (x - (x \bmod 2))/2$, and $H$ preserves Haar
   measure. This is Lagarias's theorem for $T$ with the same statement.
2. **Each class modulo $2^n$ is mapped onto $\mathbb Z_2$ by an exact similarity of ratio $2^n$** (paper; tested by
   `similarity_holds` and by every pair below $2^8$ for $n \le 3$). If $U \equiv V \pmod{2^n}$ then
   $|H^n(U) - H^n(V)|_2 = 2^n |U - V|_2$, and $H^n$ is a bijection from each class modulo $2^n$ onto $\mathbb Z_2$. So
   $H$ is exactly 2-to-1 on $\mathbb Z_2$, its two inverse branches $H_a^{-1}$ (the preimage with $u_0 = a$) are
   similarities of ratio $1/2$, and $H_a^{-1}$ is a T-function: bit $j + 1$ of $H_a^{-1}(V)$ depends on bits
   $0, \dots, j$ of $V$ only, by $u_{j+1} = v_j \oplus (u_j \lor u_{j-1})$, $u_{-1} = 0$ (`inverse_branch`; the kit's
   backward transducer `Rule30ZeroBoundary.back`).
3. **No iterate is affine on any class** (proved in Lean for the integer witnesses,
   [HeldSimilarity](../../Rule30Open/PeriodTwo/HeldSimilarity.md), `heldNat_not_affine`; the one-line step to
   $\mathbb Q_2$ is on paper; the witnesses are also checked for $n \le 12$ and every class modulo $2^k$, $k \le 6$,
   by `affinity_defect`). For every $n \ge 1$, $k \ge 0$ and $a$, there are no $\alpha, c \in \mathbb Q_2$ with
   $H^n(U) = \alpha U + c$ for every $U \equiv a \pmod{2^k}$. Where $T^n$ has the formula $(3^m x + r)/2^n$ on a
   class, $H^n$ has a similarity that is a polynomial over $\mathrm{GF}(2)$ in the bits, and no formula of degree one.
4. **K is the attractor of two nonaffine similarities** (paper; `ifs_point` reproduces every residue of $K$ modulo
   $2^{12}$ with its itinerary). Let $G_b = H_b^{-1} \circ H_1^{-1}$ for $b \in \{0, 1\}$. Each $G_b$ is a bijective
   similarity of ratio $1/4$ from $\mathbb Z_2$ onto the class $\{u_0 = b,\ u_1 = 1 - b\}$ modulo 4 ($1 + 4\mathbb Z_2$
   for $b = 1$, $2 + 4\mathbb Z_2$ for $b = 0$), and the point of $K$ with itinerary $\beta$ is
   $$\Phi(\beta) = \lim_{n \to \infty} G_{\beta_0} \circ G_{\beta_1} \circ \dots \circ G_{\beta_{n-1}}(x),$$
   for every $x \in \mathbb Z_2$, with $|\Phi(\beta) - G_{\beta_0} \circ \dots \circ G_{\beta_{n-1}}(x)|_2 \le 4^{-n}$.
   So $K = G_0(K) \cup G_1(K)$ with disjoint pieces, $|\Phi(\beta) - \Phi(\beta')|_2 = 4^{-s}$ for $s$ the first index
   where $\beta$ and $\beta'$ differ, and the dimension $1/2$ of [the structure of K](k-structure.md) is
   $\log 2 / \log 4$. Neither $G_b$ is affine on any ball. For the 3x+1 map the same construction with the affine
   branches gives Bernstein's series for the inverse conjugacy; here the branches are nonaffine on every cylinder, which
   is the metric form of the dense forced bits of [the forced bits](../../negative-results/period-two/forced-bits-dense.md).
5. **What the cycle equation becomes** (paper). A periodic itinerary $w^\infty$ of length $n$ gives the unique fixed
   point of the contraction $G_w = G_{w_0} \circ \dots \circ G_{w_{n-1}}$ of ratio $4^{-n}$ (Banach). For $T$ the fixed
   point of the affine $T$-branch is the explicit rational $r/(2^k - 3^m)$; here the fixed point is rational by the
   domain argument of `inK_periodic_rational`, with a denominator dividing $2^q - 1$ for its spatial period $q$, and
   no formula for $q$ in terms of $w$ is known (the table of item 2 of [the shift model](shift-model.md) gives $q$ up
   to 38,304 for $n = 12$). The Collatz cycle problem, hard for $T$ (Steiner; Simons and de Weger), is the easy part
   here: no periodic point is an integer, since $H$ moves the last 1 of a finite $U$ up by one cell
   (`inK_periodic_not_finite`), and for the same reason, on all of $\mathbb Z_2$, the column of an integer $U$ is eventually periodic
   only for $U \in \{0, -1\}$ (item 6). The open part is the analog of a divergent trajectory, which the 2-adic theory of $T$ leaves open as well.
6. **Lagarias's periodicity conjecture, both directions** (paper). For $T$ the conjecture is that $Q$ maps
   $\mathbb Q \cap \mathbb Z_2$ onto the eventually periodic sequences. For $H$ on all of $\mathbb Z_2$ the inclusion
   $Q^{-1}(\text{eventually periodic}) \subseteq \mathbb Q$ holds ([the shift model](shift-model.md), items 2 and 4:
   a periodic column gives a rational, and rationality passes to preimages), and the other inclusion fails: for an
   integer $U$ the column $Q(U)$ is eventually periodic exactly when $U \in \{0, -1\}$. For $U > 0$ this is the
   kit's `Rule30ZeroBoundary.col_not_eventually_periodic` in its encoding; for $U < -1$, $H(U)$ is a positive integer
   (proof below). So the analog of the periodicity conjecture is false on $\mathbb Z_2$, and the conjecture (R) of
   [the shift model](shift-model.md), its restriction to $K$, is a statement about $K$ and not about $H$.

## Proofs

**Item 1.** By `heldOrbit_triangular`, $c_t(U) = u_t \oplus g_t(u_0, \dots, u_{t-1})$. So if $U$ and $V$ first differ
at bit $k$, then $c_t(U) = c_t(V)$ for $t < k$ and $c_k(U) \ne c_k(V)$: $v(Q(U) - Q(V)) = v(U - V)$. $Q$ is onto by
`column_bijective`. $c_t(H(U)) = c_{t+1}(U)$ is $Q \circ H = \sigma \circ Q$. An isometric bijection maps each ball onto
a ball of the same radius, so it preserves Haar measure, and so does $\sigma$; hence so does $H = Q^{-1} \sigma Q$.

**Item 2.** Let $U \equiv V \pmod{2^n}$ first differ at bit $k \ge n$. For $j < k - n$, $U$ and $V$ agree below
$j + n + 1$, so `heldOrbit_triangular` at $(n, j)$ gives $H^n(U)_j = H^n(V)_j$. At $j = k - n$ they agree below $j + n$
and differ at $j + n$, so $H^n(U)_j \ne H^n(V)_j$. Hence $v(H^n U - H^n V) = k - n$. Bijectivity: $Q$ maps the class of
$a$ modulo $2^n$ onto the class of $Q(a)$ modulo $2^n$ (an isometric bijection maps each ball onto a ball of the same
radius), and $\sigma^n$ maps every class modulo $2^n$ bijectively onto $\mathbb Z_2$; conjugate by $Q$.

**Item 3.** Three lemmas on nonnegative integers. Write $\mathrm{top}(x)$ for the highest set bit and $E(x) = x \oplus
((x \ll 1) \lor (x \ll 2))$.

- *Scaling.* For $m \ge 1$, $H(x 2^m) = 2^{m-1} E(x)$: $(x 2^m) \gg 1 = x 2^{m-1}$ and
  $x 2^m \lor x 2^{m+1} = 2^{m-1}(2x \lor 4x)$. By induction $H^n(x 2^m) = 2^{m-n} E^n(x)$ for $m \ge n$.
- *Separation.* If $A, B \ge 0$ and every set bit of $B$ is at least $\mathrm{top}(A) + 3$ (or $A = 0$), then
  $H(A + B) = H(A) + H(B)$, the set bits of $H(B)$ are at least the lowest bit of $B$ minus 1, and
  $\mathrm{top}(H(A)) = \mathrm{top}(A) + 1$ (`held_topBit`). Bit $j$ of $H$ reads bits $j - 1, j, j + 1$. For
  $j \le \mathrm{top}(A) + 1$ these lie below the lowest bit of $B$, so bit $j$ of $H(A + B)$ is bit $j$ of $H(A)$ and
  bit $j$ of $H(B)$ is 0; for $j \ge \mathrm{top}(A) + 2$ they lie above $\mathrm{top}(A)$, so bit $j$ is bit $j$ of
  $H(B)$ and bit $j$ of $H(A)$ is 0. The supports are disjoint, so the OR is a sum. Each step narrows the gap by at
  most 2.
- *Size.* For $x > 0$ with top bit $p$, bits $p + 2$ and $p + 1$ of $E(x)$ are $x_{p+2} \oplus (x_{p+1} \lor x_p) = 1$
  and $x_{p+1} \oplus (x_p \lor x_{p-1}) = 1$, and higher bits are 0. So for $n \ge 1$, $E^n(1)$ has top bit $2n$ and
  bit $2n - 1$ set, $E^n(1) \ge 3 \cdot 2^{2n-1}$ and $3 E^n(1) \ge 9 \cdot 2^{2n-1} > 2^{2n+2}$, while $E^n(3)$ has
  top bit $2n + 1$ and $E^n(3) < 2^{2n+2}$. Hence $E^n(3) \ne 3 E^n(1)$.

Now take the integer representative $0 \le a < 2^k$ and $m = k + 2n + 3$. The integers $a + 2^m$ and $a + 3 \cdot 2^m$
lie in the class. With $A = a$ and $B = x 2^m$, $x \in \{1, 3\}$, the gap is at least $m - k + 1 \ge 2n + 4$, so it stays
at least 3 for $n$ steps and $H^n(a + x 2^m) = H^n(a) + 2^{m-n} E^n(x)$. If $H^n(U) = \alpha U + c$ on the class, then
$H^n(a + 3 \cdot 2^m) - H^n(a) = 3 (H^n(a + 2^m) - H^n(a))$, that is $E^n(3) = 3 E^n(1)$, which the size lemma excludes.
(The values for $n = 1, \dots, 4$: $E^n(1) = 7, 25, 111, 401$ and $E^n(3) = 13, 51, 221, 803$.)

**Item 4.** By item 2, $H_a^{-1}$ exists for every $a$ and is a bijective similarity of ratio $1/2$ onto
$\{u_0 = a\}$. $U = G_b(W)$ has $u_0 = b$, $H(U) = H_1^{-1}(W)$ has bit 0 equal to 1, so $c_1(U) = 1$, that is
$u_1 \oplus u_0 = 1$, and $H^2(U) = W$. So $G_b$ is the inverse of $H^2$ on the class $\{u_0 = b, u_1 = 1 - b\}$, and
for $W \in K$, $G_b(W)$ is the preimage of $W$ in $K$ with first reading $b$ (`held_held_two_to_one`). Hence
$\Phi(\beta) = G_{\beta_0}(\Phi(\sigma \beta))$, and iterating, $\Phi(\beta) = G_{\beta_0} \circ \dots \circ
G_{\beta_{n-1}}(\Phi(\sigma^n \beta))$; replacing $\Phi(\sigma^n \beta)$ by any $x$ moves the result by at most
$4^{-n}$. Two itineraries first differing at $s$ give points agreeing below bit $2s$ (item 1 of the shift model) and
differing at bit $2s$, since $\beta_s = u_{2s} \oplus g_{2s}(\text{lower bits})$. If $G_b$ were affine on a ball $B$,
then $G_b(B)$ is a ball (a bijective similarity onto a class modulo 4 maps balls onto balls), and $H^2 = G_b^{-1}$
would be affine on it, against item 3 with $n = 2$.

**Item 6.** If $U = -1 - V$ with $V \ge 0$ finite, every bit of $U$ at or above $\mathrm{top}(V) + 1$ is 1, so bit
$j \ge \mathrm{top}(V) + 2$ of $H(U)$ is $1 \oplus (1 \lor 1) = 0$: $H(U)$ is a nonnegative integer. $H(U) = 0$ only for
$U \in \{0, -1\}$: the preimages of 0 satisfy $u_{j+1} = u_j \lor u_{j-1}$ and $u_1 = u_0$, which gives all zeros or
all ones. A positive integer has a column that is not eventually periodic (the kit's `col_not_eventually_periodic`;
also directly: an eventually periodic column makes $H^s(U)$ a fixed point of $H^q$ by the injectivity of $Q$, and a
nonzero finite point moves its last 1, `heldOrbit_topBit`). $Q(0) = 0$ and $Q(-1) = 1$ are eventually periodic.

## What it means

The 2-adic dictionary between $T$ and $H$ is exact in its metric part: isometric conjugacy to the shift, Haar measure,
exact 2-to-1 expansion by 2, and a set of the problem that is a self-similar Cantor set. It breaks at the algebra: the
3x+1 map is affine on classes, which makes each cycle an explicit rational and the inverse conjugacy an explicit series,
and $H$ is affine on no class for any number of steps. So the tools that use the affine form (the cycle equation with
its denominators $2^k - 3^m$, Bernstein's series, the bounds on cycles from linear forms in logarithms) have nothing to
act on, and the ones that use only the metric part (Haar measure, density statements) give exact but trivial results
here ([the Collatz technology](../../negative-results/period-two/collatz-technology.md)). The question that is hard in
both problems, whether an integer can have an aperiodic itinerary in the set of the problem, is the part neither
dictionary reaches.

## Reproduce

```bash
python -m computations.held_similarity --max-n 12
```

It prints $E^n(1)$, $E^n(3)$ and $3 E^n(1)$ for $n \le 12$, checks the similarity of ratio $2^n$ on 200 random pairs
for each $n$, and checks the nonaffinity witness on every class modulo $2^k$, $k \le 6$, in under a second.
`tests/test_held_similarity.py` checks $H(x 2^m) = 2^{m-1} E(x)$, the similarity on every pair below $2^8$ by stepping
integers, the inverse branch, the witnesses with the size inequality, and that `ifs_point` gives exactly the
$2^6$ residues of $K$ modulo $2^{12}$ of `held_shift.forced_halves`, each with its itinerary.
