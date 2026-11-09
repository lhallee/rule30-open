---
title: Every route tried toward L_n / n unbounded for the single cell's right edge stops at a parity over the middle of a period; bit filling holds only right after a doubling, the two edges fix one end of the expansions, counting and renormalization return to the white runs, no GF(2) rule of at most three terms among 18 weight parities predicts a doubling except its definition, and the seeds ±1/3 and Rule 150 bar any argument without the light cone and the product term
category: complexity
problems: [3]
status: negative
kind: dead-end
evidence: [computations/right_edge_runs.py, computations/right_edge_runs.c, tests/test_right_edge_runs.py]
---

# Every route tried toward L_n / n unbounded for the single cell's right edge stops at a parity over the middle of a period; bit filling holds only right after a doubling, the two edges fix one end of the expansions, counting and renormalization return to the white runs, no GF(2) rule of at most three terms among 18 weight parities predicts a doubling except its definition, and the seeds ±1/3 and Rule 150 bar any argument without the light cone and the product term

**Question.** [Right-edge cycles](../../findings/complexity/right-edge-cycles.md) conjectures that the cycle length
$L_n$ of 1 under $\Phi(x) = x \oplus (2x \lor 4x)$ modulo $2^n$ grows faster than linearly, which by
[TwoIndex](../../Rule30Open/Complexity/TwoIndex.md) would make Rule 30's diagram not 2-automatic in two indices. In the
notation of that entry, $R_j$ is the $j$-th diagonal from the right edge, of least period $P_j = L_{j+1}$, Mahler degree
$K_j$ and input $g_j = R_{j-1} \lor R_{j-2}$; $J_k = W(2^k)$ is the white run beside the right edge at time $2^k$, and the
stall at period $2^{k+1}$ is the run of $d_k = J_{k+1} - J_k$ diagonals of that period. The conjecture holds if
$d_k = o(2^k)$, or if $J_{k+1} \le \lambda J_k + C$ for some $\lambda < 2$ (Proposition D there). The entry proves that a
stall lasts one diagonal if and only if $R_{J_k}$ has an odd number of black cells in $2^k$ (Theorem A), two if and only
if a second parity is odd (Theorem B), and that after that each doubling is the parity of the black cells of the
half-period difference of an input (Lemma 2). Does any of these laws, or the structure around them, bound $d_k$?

**What was done.** Seven routes, each followed to the step where it stops. The numbers come from
`computations/right_edge_runs.py`: the laws and the candidate lemmas by level lifting to period $2^{27}$ (diagonals
$j \le 65$, `laws`), the search for linear rules among weight parities on $3 \le j \le 64$ (`weights`), the isometries
$\varphi_k$ modulo 16 for $k \le 18$ by `computations/right_edge_runs.c` (`phi`), and the seeds $\pm 1/3$ and Rules 150 and
90 (`barriers`). `tests/test_right_edge_runs.py` checks each against an independent computation.

## 1. Bit filling

**Idea.** The bit-filling guess says $K(f \lor g) = K(f) \lor K(g)$, the bitwise or of the Mahler degrees. For the
inputs it would make $K(g_j)$, and with it every doubling (the top coefficient $a_{P-1}$ of the input), a recursion on the
integers $K_j$.

**What holds.** The guess is exact at the first diagonal after a doubling: if diagonal $i \ge 3$ doubles and $i + 1$ does
not, $K(g_{i+1}) = K_i \lor K_{i-1}$. Theorem A of the finding gives $K_{i+1} = H + K_{i-1} + 1$ with $H = P_{i-1}$;
$g_{i+1}$ has an even number of black cells in a period, so $K(g_{i+1}) = K_{i+1} - 1 = H + K_{i-1}$; and $K_i = H$ is one
binary digit above $K_{i-1} < H$.

**What fails** (computed, $2 \le j \le 65$). $K(g_j) \ge K_{j-1} \lor K_{j-2}$ fails at 11 diagonals,
$j = 2, 12, 13, 14, 19, 21, 22, 23, 32, 33, 46$. At all of them but $j = 46$ the or is $P_{j-1} - 1$, so the guess
predicts a doubling that does not happen; at the 37 diagonals where the or is below $P_{j-1} - 1$, it fails only at
$j = 46$. Even $K(g_j) \ge \max(K_{j-1}, K_{j-2})$ fails, at 10 diagonals ($j = 2, 12, 13, 14, 19, 21, 22, 32, 33, 46$):
the degree of the input can fall below that of both diagonals. Equality holds at 21 diagonals that do not double: the
18 that follow a doubling diagonal $i \ge 3$, and $j = 20, 47, 62$.

**Where it stops.** Monomials multiply by the union of binary digits, $\binom{t}{i}\binom{t}{i'} \equiv \binom{t}{i \lor
i'} \pmod 2$ (Lucas), so $a_m(f \lor g) = a_m(f) + a_m(g) + \sum_{i \lor i' = m} a_i(f)\, a_{i'}(g)$: the degree of
$f \lor g$ is the largest $m$ at which this sum is odd, and the guess keeps only the pair $(K(f), K(g))$. The doubling of
diagonal $j + 1$ is the coefficient at $m = P_j - 1$, the parity of a count of pairs over supports of size of order
$P_j$, and nothing in the recursion orders these counts.

## 2. More of the left edge, or of the seed's past

**Idea.** The two ends of a period of $R_j$ are regular. At the start, $R_j(t) = 0$ for $2t < j$ and
$R_j(\lceil j/2 \rceil) = 1$ (the kit's `Rule30RightPeriods.R_lt`, `R_half`), and the left diagonals, which settle at
about time $4i/3$ at depth $i$ on the range of [the onset edge](../../findings/diagonals/onset-edge.md) (a gain of 0.752
depth per step), make $R_j$ regular to about time $4j/5$ (a heuristic reading of that gain: the cell $(t, t - j)$ lies
on the left diagonal $2t - j$). At the end, the agreement identity of the finding with $a = P - s$ and $b = -s$ says
that $R_j(P - s)$ is bit $j$ of $h(-s)$, the row of the seed's past at time $-s$, for every $j$ whose period divides
$P$; that row is periodic beyond its preperiod, which is 1,509, 4,968 and 15,615 cells at $s = 300$, 1,000 and 3,000
([the seed's past](../../findings/frames/seed-past.md)), so the end of a period is regular for $s$ up to about $j/5$
(again a heuristic reading). More regular data at both ends might decide the doubling parity.

**Where it stops.** Values on a first window $[0, w)$ fix the Mahler coefficients $a_k(f)$, $k < w$, since $a_k(f)$ sums
$f(s)$ over the $s$ whose binary digits are digits of $k$. Values on a last window $(P - 1 - w', P)$ fix the dual
coefficients $c_a(f) = \sum_{t \supseteq a,\ t < P} f(t)$ for $a > P - 1 - w'$, the sums over the $t$ whose digits
contain those of $a$. The doubling of diagonal $j + 1$ is the parity of $|R_j| + |R_{j-1}| + |R_j R_{j-1}|$ over
$P = P_j$, and expanding $f(t) = \sum_{i \subseteq t} a_i(f)$ gives $|fg| \equiv \sum_{i < P} a_i(f)\, c_i(g)$ modulo 2.
Let $P \ge 2(w + w')$. A term with $i < w$ has the factor $c_i(g)$, a sum that contains $g(i + P/2)$; a term with
$i > P - 1 - w'$, so $i \ge P/2$, has the factor $a_i(f)$, a sum that contains $f(P/2)$; the terms in between have
neither factor fixed. So every term of $|fg|$, like $|f|$ and $|g|$ themselves, contains a cell outside both windows, in
the middle of the period: the edges enter the doubling only as factors of chaotic data. The windows have length linear
in $j$, so (a heuristic reading) an argument from them alone gives a bound of the order of the kit's linear ones
(`Rule30RightPeriods.period_gt`, `per_bound`, from the light cone).

## 3. Counting on the restart

**Idea.** Count how the pattern restarts at the right edge: how often rows agree near the edge, how many distinct words
of $n$ cells end a row.

**Where it stops.** By the agreement identity of the finding, $v_2(h(a) - h(b)) = J_{v_2(a - b)} + 1$ for all integers
$a \ne b$: how far two rows agree depends on $v_2(a - b)$ alone, through the $J_k$. So every such count is a statement
about the $J_k$ again; the number of distinct words of $n$ cells that end a row is $L_n$ itself, since $h(\tau)$ modulo
$2^n$ depends on $\tau$ modulo $L_n$ only. The identity $v_2(h(t) - 1) = v_2(h(-t) - 1)$ between the white runs of the
future and of the past is its case of the pairs $(t, 0)$ and $(-t, 0)$. Counting the black cells of a diagonal or of an
input over the two halves of a period gives the parity of a half-period difference, which is how Lemma 2(b) already
states the doubling.

## 4. Weights modulo 2 or 4

**Idea.** Find an identity among weights over one period (numbers of black cells, as integers) that predicts the
doubling bit without being its definition.

**What holds.** At a diagonal $j$ that does not double, summing $R_j(t + 1) = R_j(t) + g_j(t) - 2R_j(t) g_j(t)$ over a
period gives $|g_j| = 2|R_j g_j|$, so $|g_j|/2$ is the number of black runs of $R_j$; and summing
$R_j(t) = \sum_{s < t} g_j(s)$ gives $|R_j| \equiv \sum_{s \text{ odd}} g_j(s) \pmod 2$. The doubling of diagonal $j + 1$
is the parity of $|R_j| + |R_{j-1}| + |R_j R_{j-1}|$, weights over $P_j$.

**What fails** (computed, $3 \le j \le 64$). Take the nine weights over $P_j$: $|R_j|$, $|R_{j-1}|$, $|R_j R_{j-1}|$,
$|R_j R_{j-2}|$, $|R_{j-1} R_{j-2}|$, $|R_j R_{j-1} R_{j-2}|$ and the first, second and third counted at odd times only;
each modulo 2 and its second binary digit, 18 parities, and the constant 1. Among the 1,159 GF(2)-linear rules with at
most three of these 19 terms, the only one that gives the doubling bit of diagonal $j + 1$ at all 62 diagonals is the
defining identity $|R_j| + |R_{j-1}| + |R_j R_{j-1}|$.

**Where it stops.** Each step down the diagonals asks for the weights of the previous ones at a finer residue: $|R_j|$
modulo 2 is the weight of $g_j$ at odd times, which needs the weights of $R_{j-1}$, $R_{j-2}$ and their product at odd
times, and those need residues modulo 4, and so on. No relation beyond the definition appears on the range searched.
The kit's `Rule30LocalConservation` (every integer density conserved by four steps of Rule 30 is a constant plus a
coboundary) agrees with this; no obstruction was derived from it.

## 5. Renormalization

**Idea.** With $\nu_k = J_k + 1$, put $\varphi_k(y) = (\Phi^{2^k}(1 + 2^{\nu_k} y) - 1)/2^{\nu_k}$. $\Phi^{2^k}$ maps the
ball $1 + 2^{\nu_k}\mathbb{Z}_2$ onto itself isometrically, since $h(2^k) \equiv 1$ modulo $2^{\nu_k}$, so $\varphi_k$ is
an isometry of the 2-adic integers; $\varphi_k^2(0) = (h(2^{k+1}) - 1)/2^{\nu_k}$ has valuation
$\nu_{k+1} - \nu_k = d_k$; and iterating $\Phi^{2^k}(1 + 2^{\nu_k} x) = 1 + 2^{\nu_k} \varphi_k(x)$ twice at
$x = 2^{d_k} y$ gives
$$\varphi_{k+1}(y) = 2^{-d_k}\, \varphi_k^2(2^{d_k} y).$$
So the $J_k$ come from iterating one map on isometries, from $\varphi_0(y) = (\Phi(1 + 2y) - 1)/2$, and $d_k$ is read off
$\varphi_k$ modulo $2^{d_k + 1}$. A fixed point of this map, or a finite set of isometries that it maps into itself and
that contains $\varphi_0$, would make $\varphi_k$, and with it $d_k$, eventually periodic, so bounded.

**What fails** (computed, $k \le 18$). The maps $\varphi_k$ modulo 16 are 19 distinct permutations of $\mathbb{Z}/16$,
none of them affine; for instance $\varphi_5 = (5, 12, 7, 6, 9, 0, 11, 10, 13, 4, 15, 14, 1, 8, 3, 2)$, whose square sends
0 to 0 modulo 16 ($d_5 = 6$). The transducers of $\Phi^{2^k}$ grow at every squaring for $k \le 4$
([automaton-group sections](automaton-group-sections.md)).

**Where it stops.** The renormalization by itself constrains nothing. For an affine isometry $\varphi(y) = ay + b$ with
$a$ and $b$ odd, it gives $d = v_2(a + 1)$ and then $\varphi'(y) = a^2 y + b(a + 1)/2^d$, so every later $d$ is
$v_2(a^2 + 1) = 1$; any first stall occurs, then stalls of one diagonal. And Rule 150, whose right-edge map is an
isometry with the same identity, has $d_k = 2^k$ (section 7). What decides $d_k$ is the particular $\varphi_0$, and no
finite structure appears in its renormalizations on the range.

## 6. Structure forces even parities

**Idea.** Find an exact law that makes some doubling parity odd inside the middle of a period.

**Where it stops.** Every exact parity law available comes from the half-period complement of a doubling diagonal. It
either carries a parity from the previous period (Theorem A(i): the double doubling is decided by the weight of the last
diagonal of the previous period) or makes a count a multiple of $H$ (the kit's `Rule30RightPeriods.no_three`: the parity
a diagonal accumulates over $4H$ steps is the number of white cells of another in $2H$ steps, which is $H$). Lemma 2(b)
and Theorem B only rewrite the remaining decisions as parities over the middle of a period. The only odd count that
the known structure produces is the light cone's: if $R_{2P-3}$ and $R_{2P-2}$ had period $P$, each would have the single
black cell $t = P - 1$ in $[0, P)$, so the input of diagonal $2P - 1$ would have one black cell and that diagonal doubles;
this is the kit's linear bound $J_k \le 2^{k+1} - 2$ (`per_bound`). A superlinear bound needs a source of odd parity in
the middle of a period, and none was found.

## 7. Two barriers

- **The seeds $\pm 1/3$.** $\Phi$ swaps the 2-adic integers $1/3 = \dots 01011$ and $-1/3 = \dots 0101$ (the kit's
  `Rule30EdgeStaircases.period_two_iff`; checked modulo $2^{128}$), so their cycles modulo $2^n$ have length 2 for every
  $n \ge 2$. Lemma 1 of the finding, Proposition D, the renormalization, and the agreement identity in the form "how far
  $\Phi^a(y)$ and $\Phi^b(y)$ agree depends on $v_2(a - b)$ only" (which needs only that $\Phi$ is an isometry whose
  cycles modulo $2^n$ have lengths that are powers of two) hold for the orbit of every 2-adic seed $y$, so an argument
  built from them alone would prove the conjecture for $\pm 1/3$ as well, which is false. The kit's
  `inp_least_period`, used in item 5(a) and Lemma 2 of the finding, rests on the light cone of the finite seed; a proof
  has to use it.
- **Linearity.** Rule 150 in the same frame, $\Phi_{150}(x) = x \oplus 2x \oplus 4x$, has
  $R_j(t) = \sum_i \binom{t}{i}\binom{i}{j - i} \bmod 2$, so $K_j = j$, $P_j = 2^{\lceil \log_2(j+1) \rceil}$ and
  $J_k = 2^k - 1$: its cycle lengths grow linearly. It shares the frame, the isometry, the white region $R_j(t) = 0$ for
  $2t < j$, the doubling criterion, Lemma 1 and item 5(a) of the finding, and lacks only the product term of
  $R_{j-1} \lor R_{j-2} = R_{j-1} \oplus R_{j-2} \oplus R_{j-1} R_{j-2}$. Rule 90, $\Phi_{90}(x) = x \oplus 4x$, has
  $R_{2m}(t) = \binom{t}{m} \bmod 2$, $K_{2m} = m$, white odd diagonals and $J_k = 2^{k+1} - 1$. (Computed for $j < 64$
  by level lifting with the gates xor and the older input; the test checks the lifted diagonals against a direct run of
  the rule tables.) A proof has to use the product term, which by section 1 enters a doubling only through parities of
  counts of pairs.

## What it means

A proof that $L_n / n$ is unbounded has to combine the light cone, which separates the single cell from the seeds
$\pm 1/3$, with the product term, which separates Rule 30 from Rule 150, and produce an odd count inside the middle of a
period: the form here of the statement that the chaotic part of a row behaves fairly, at which the routes of
[the roadmap](../../ROADMAP.md) stop. The cleanest sufficient statements are $d_k = o(2^k)$, which by the anatomy of a
stall says that the hovering runs are $o(2^k)$ long; $J_{k+1} \le \lambda J_k + C$ with $\lambda < 2$ (Proposition D;
$\lambda = 1.75$ holds for $1 \le k \le 35$); and its agreement form
$v_2(h(2^k) - h(-2^k)) \le \lambda\, v_2(h(2^k) - 1) + C'$.

## Reproduce

```bash
python -m computations.right_edge_runs laws --diagonals 66      # sections 1, 3, 6: about 5 s, 1.5 GB
python -m computations.right_edge_runs weights --diagonals 66   # section 4: about 5 s, 2 GB
python -m computations.right_edge_runs phi --k-max 18        # section 5: under a second
python -m computations.right_edge_runs barriers              # section 7: about a second
```
