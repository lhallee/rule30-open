---
title: The cycle data of the right-edge map fix the center column only at the times t with L_t dividing t, since a map that keeps every cycle length and differs from Rule 30's on a set of measure at most 2^(2 - t0) reads any prescribed word on the diagonal at every other time from t0 on
category: frames
problems: [1, 2]
status: negative
kind: barrier
evidence: [computations/diagonal_freedom.py, tests/test_diagonal_freedom.py]
---

# The cycle data of the right-edge map fix the center column only at the times t with L_t dividing t, since a map that keeps every cycle length and differs from Rule 30's on a set of measure at most 2^(2 - t0) reads any prescribed word on the diagonal at every other time from t0 on

**Question.** In the frame of its right edge the single cell is the orbit of 1 under the 2-adic map $\Phi(y) = y \oplus
(2y \lor 4y)$, an invertible T-function (bit $i$ of $\Phi(y)$ is $y_i$ plus a function of the lower bits), and the
center column is its diagonal, $c(t) = $ bit $t$ of $\Phi^t(1)$. The structure of the cycle lengths $L_n$ of 1 modulo
$2^n$ (powers of two that double exactly at the odd parities), the odometer structure of the orbit closure and the
measure-theoretic properties of $\Phi$ are in the kit (`TFunction`, `TFunctionCycles`, `Odometer`), and $L_n$ is
computed to $n = 84$ ([right-edge cycles](../../findings/complexity/right-edge-cycles.md)); the growth of $L_n$ is open.
Can an argument built from such data decide whether the diagonal is eventually periodic, or how often it is black?

**Outcome.** No. The data fix bit $t$ of $\Phi^t(1)$ only at the times $t$ with $L_t \mid t$. By the kit's
`Rule30RightPeriods.per_bound` ($L_t \ge (t + 1)/2$) these are powers of two with $L_t = t$: here $t = 1, 2, 4$, and
none with $5 \le t \le 84$. At every other time from $t_0$ on, the data allow either value.

**Theorem (diagonal freedom; proved on paper).** Let $F$ be an invertible T-function, bit $i$ of $F(y)$ equal to $y_i
\oplus f_i(y \bmod 2^i)$, let $x$ be a seed with cycle lengths $L_i$ modulo $2^i$ and doubling parities $\pi_i$
($L_{i+1} = L_i(1 + \pi_i)$), let $t_0 \ge 1$, and let $d : \mathbb{N} \to \{0, 1\}$ be any sequence. There is an
invertible T-function $G$, with level functions $g_i$, such that

1. $g_i = f_i$ for $i < t_0$, so $G = F$ modulo $2^{t_0}$;
2. for $i \ge t_0$, $g_i$ and $f_i$ differ at no more than two residues modulo $2^i$, so $G$ and $F$ differ on a set of
   Haar measure at most $\sum_{i \ge t_0} 2 \cdot 2^{-i} = 2^{2 - t_0}$;
3. $x$ has the same cycle length $L_i$ under $G$ as under $F$, at every level;
4. for every $t \ge t_0$ with $L_t \nmid t$, bit $t$ of $G^t(x)$ is $d(t)$; when $L_t \mid t$ it is
   $x_t \oplus (t/L_t)\pi_t$, the same for every map with these cycle lengths.

*Proof.* Build $g_i$ level by level, keeping the $G$-cycle of $x$ modulo $2^i$ of length $L_i$. Let $o_s = G^s(x) \bmod
2^i$, distinct for $s < L_i$, and $u(s) = g_i(o_s)$. Bit $i$ of $G^s(x)$ is $x_i \oplus \sum_{r < s} u(r)$, the sum
taken around the cycle, so with $t = i = qL_i + r$, $0 \le r < L_i$, it is $x_i \oplus qP \oplus \sum_{s < r} u(s)$,
where $P = \sum_{s < L_i} u(s)$ is the parity of the level. Start from $u = f_i(o_s)$. If $r \ge 1$, flip $u$ at $o_0$
if needed to make $x_i \oplus q\pi_i \oplus \sum_{s < r} u(s) = d(i)$. In every case, then flip $u$ at $o_{L_i - 1}$,
which is at or after $r$, if needed to make $P = \pi_i$: the changes at lower levels move the orbit modulo $2^i$, so
$\sum_s f_i(o_s)$ need not be $\pi_i$, even when $r = 0$. Then $L_{i+1} = L_i(1 + P)$ is unchanged. Bit $i$ of $G^i(x)$
is $d(i)$ when $r \ge 1$, and the forced value $x_i \oplus q\pi_i$ when $r = 0$. Any family of level functions defines
an invertible T-function. $\square$

If $L_i \ge i + w$ for every $i \ge t_0$, the same flips at the orbit times before $i, i + 1, \dots, i + w - 1$
prescribe the bits $i$ of $G^i(x), \dots, G^{i+w-1}(x)$ together. Each level then changes up to $w + 1$ residues, so $G$
and $F$ differ on a set of measure at most $(w + 1)2^{1 - t_0}$. For Rule 30, $L_i \ge i + 2$ for $5 \le i \le 84$
([right-edge cycles](../../findings/complexity/right-edge-cycles.md)), while the kit proves only $L_i \ge (i + 1)/2$
(`Rule30RightPeriods.per_bound`). With $w = 2$ these bits are the center at time $i$ and column 1 at time $i + 1$. So if
$L_i \ge i + 2$ for every $i \ge t_0$, two adjacent columns can be prescribed at once, and Jen's theorem, that no two
adjacent columns are eventually periodic, is not a consequence of the T-function structure, the cycle lengths, or any
property of $\Phi$ that holds off a set of measure $3 \cdot 2^{1 - t_0}$.

**The center-override form for Rule 30.** For $F = \Phi$ and $x = 1$, if $L_i > i$ at every level $i \ge t_0$ (true for
$5 \le i \le 84$, not proved beyond; the kit gives $L_i \ge (i + 1)/2$), put the flips at the orbit times $i - 1$ and
$L_i - 1$ only. Then the map $G$ keeps the light cone and both edges ($G^s(1)$ has exactly $2s + 1$ binary digits).
Along the orbit it differs from Rule 30 only at the center cells where the prescribed word differs from the rule, and at
the times $t \ge L_i$ on each right diagonal $i$; at a doubling diagonal some of these lie inside its least period
$L_{i+1}$. So the left half of the $G$-world evolves exactly by Rule 30 driven by the prescribed center column.
`computations/diagonal_freedom.py` checks this by direct iteration to 40 levels with $t_0 = 8$ for four prescribed words
(all white, all black, $(10)^\infty$, $(110)^\infty$): the cycle lengths, the readout, the light cone and both edges
hold, and the Rule 30 law fails only at 15 to 20 center cells and at 10 to 13 cells with $L_i \le t < L_{i+1}$, never
before $L_i$. On 300 random invertible T-functions of 10 levels the construction of the theorem keeps every cycle
length, gives the prescribed or forced readout, and changes at most two residues per level.

**What it means.** No argument whose ingredients hold in the modified world can prove Problem 2, and none can prove
Problem 1 if the times $t$ with $L_t \mid t$ are finite in number (true if $L_t > t$ for every large $t$, which the
computed range supports and nothing proves). The ingredients are $\Phi$ modulo any fixed $2^{t_0}$; the cycle lengths,
the doubling parities and the odometer structure; the antiperiodic diagonals at doubling levels; and any property of the
map off a set of small measure. If also $L_i > i$ for every $i \ge t_0$, the center-override form adds the light cone,
both edges, and the Rule 30 law at every cell but the center column and the cells at times $t \ge L_i$ on each right
diagonal $i$. For Problem 2, take $d$ white: the center is then black at most at the forced times, which are powers of
two. The kit's `TFunctionCycles.exists_diagonal_prefix` is the seed-side statement (for a fixed map every readout comes
from some seed); this is the map-side one (for a fixed seed every readout comes from a map with the same cycle data). A
proof has to use the Rule 30 law at the center, the coupling $c(t + 1) = x_{-1}(t) \oplus (c(t) \lor x_1(t))$, or at the
cells that the flips change. The kit's own remark in `TFunctionCycles`, that none of its cycle results reaches the
center column, is here a theorem. The same holds for every 2-adic reformulation recorded in
[reformulations](../dynamics/reformulations.md) that uses only cycle data.

## Reproduce

```bash
python -m computations.diagonal_freedom --override 40 8   # the center-override form, four words (about 45 s)
python -m computations.diagonal_freedom --random 10 300   # the theorem on random T-functions (about 1 s)
```

`tests/test_diagonal_freedom.py` checks the bitwise map against the closed form of $\Phi$, the cycle lengths against a
direct orbit, and both constructions on small cases.
