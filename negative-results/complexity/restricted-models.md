---
title: Restricted models give the center cell no new lower bound for every n; past reading the digits they imply Problem 1, and spacetime bounds hold for Rule 90
category: complexity
problems: [3, 1]
status: negative
kind: barrier
evidence: [computations/restricted_models.py, tests/test_restricted_models.py]
---

# Restricted models give the center cell no new lower bound for every n; past reading the digits they imply Problem 1, and spacetime bounds hold for Rule 90

**Question.** Is there a restricted model of computation in which a lower bound for the fixed function $n \mapsto c(n)$
can be proved for every $n$, is new, and stops short of Problem 1? Two families of models were tried: models that read
the binary digits of $n$ (one-tape machines, automata, ordered decision diagrams, communication between sets of
digits), and models confined to the spacetime diagram of the single black cell (simulating a strip of columns, and
deriving cells by the rule).

**Outcome.** In the first family a lower bound that exceeds the cost of reading the digits by an unbounded amount
implies Problem 1; below that, unbounded one-tape time is equivalent to excluding eventual periods that are powers of
two, and time $\lfloor \log_2 n \rfloor + 2$ on every $n$ to $c$ being constant on no dyadic progression; both hold on
the ranges computed and are open for every $n$. In the second family two bounds hold for every $n$ and are proved
below, but Rule 90, whose center column is white at every time after 0, meets them too, so they bound the model and
not the function.

## 1. Models that read the digits of n

*Lemma.* If $c$ has period $P$ from time $T_0$, it is computed by a one-tape machine in the kit's model in
$\ell + O(1)$ steps, $\ell$ the number of digits (one pass that computes $n \bmod P$ with an automaton and keeps $n$
exactly while it has few digits, then a table), and in $O(1)$ steps when $P$ is a power of two (read the lowest $k$
digits, $2^{k-1} \ge T_0$ and $2^k$ a multiple of $P$, then a table); by an automaton with $O(P + T_0)$ states; by an
ordered decision diagram of width $O(P + T_0)$ in every order of the digits, since $n \bmod q$ is a sum of
contributions of single digits in any order; and by a one-way protocol between any two sets of digits with
$\lceil \log_2 P \rceil + O(1)$ bits. So in each of these models a lower bound for $c$ that tends to infinity implies
Problem 1, as [the crossing-sequence entry](one-tape-crossing.md) found for automata with several passes and for
crossing sequences. For one tape the rungs are, for every machine that computes $c$:

| Lower bound on the time $T(n)$ | Relation to the problems | Status |
|---|---|---|
| $T$ unbounded | equivalent to: $c$ has no eventual period that is a power of two; implied by Problem 1 | open; for $k \le 13$ the kit proves $T > k$ infinitely often, computed here for $k \le 20$ |
| $T(n) \ge \lfloor \log_2 n \rfloor + 2$ for every $n \ge 1$ | implies the first rung; not a consequence of Problems 1 and 2 | open; the kit proves it for $n < 16$, computed here for $n < 2^{16}$ |
| $T(n) - \ell(n)$ unbounded | implies Problem 1 (the lemma) | open |
| $T$ not $o(\ell \log \ell)$ | equivalent to: $c$ is not 2-automatic (the kit's `OneTapeRegular`, `OneTapeGap`) | open |
| $T(n) \ge C n$ infinitely often, every $C$ | the kit's `Problem3` | open |

*First rung.* The kit's
[`Rule30Problem3Bounds`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/a09f245/lean/Ruliology/CellularAutomata/Rule30Problem3Bounds.lean)
(merged into the kit's main branch after the commit pinned here) proves that a machine whose run on $n$ takes at most
$k$ steps reads only the lowest $k$ digits, so time at most $k$ from any $N$ on makes $c$ periodic with period $2^k$ from
$2^{k-1}$ on (`period_of_eventually_time_le`), and time at most $k$ on the $2^k$ inputs $[2^{k-1}, 2^{k-1} + 2^k)$ alone
does the same (`period_of_canon_window_time_le`). The converse is the lemma's power-of-two case. So unbounded time is
equivalent to excluding eventual periods $2^a$, and for each $k$ it needs one pair $m \ge 2^{k-1}$ with
$c(m) \ne c(m + 2^k)$: a finite check, with a transient fixed in advance, unlike Problem 1. The least such $m$, for
$k = 1, \dots, 20$, is $2^{k-1}$ plus

| $k$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| offset | 1 | 1 | 0 | 1 | 5 | 0 | 4 | 0 | 0 | 3 | 2 | 4 | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |

so for every $k \le 20$ every machine computing $c$ takes more than $k$ steps on some input of the window and on
infinitely many inputs (the kit's own bound stops at $k = 13$, from `Rule30FactorWindow`). The offsets show no pattern (a heuristic reading, not a
test): the first pair already differs for 9 of the 20 values of $k$, about half as for a random sequence, and no offset exceeds 5.
For all $k$ this is the statement that $c$ has no eventual period $2^a$, which Problem 1 implies and nothing here
proves.

*Second rung.* The kit's `computes_const_on_dyadic_ray` makes $c$ constant on the ray
$\{m \ge 2^{k-1} : m \equiv n \pmod{2^k}\}$ when a machine halts within $k$ steps on one input $n \ge 2^{k-1}$ of it. So
if every ray modulo $2^k$ has both colors, every machine takes at least $k + 1$ steps on every $n \ge 2^{k-1}$, and if
this holds for every $k \le K$, then $T(n) \ge \lfloor \log_2 n \rfloor + 2$ for every $n < 2^K$: the machine reads
every digit and one more cell. In the first $3 \cdot 2^{19} + 64$ cells every ray has both colors for every
$k \le 16$ (the deepest first change is at ray element 17, for $k = 15$), so every machine takes at least
$\lfloor \log_2 n \rfloor + 2$ steps on every $n < 2^{16}$ and at least 17 steps on every $n \ge 2^{15}$; beyond $k = 16$
the data hold too few elements of each ray (at $k = 17$, 130,955 of the 131,072 rays change color within them). For every $n$ the
statement says that $c$ is constant on no progression $\{n + i\,2^{\ell(n)} : i \ge 0\}$. It is not a consequence of
Problems 1 and 2: a sequence with density $1/2$ and no eventual period can still be constant on such a progression.

## 2. Models confined to the spacetime diagram

Write $x(s, j)$ for the cell at time $s$ and column $j$ of the single black cell, $c(n) = x(n, 0)$. Rule 30 is
left-permutive: $x(s + 1, j) = x(s, j - 1) \oplus (x(s, j) \lor x(s, j + 1))$ flips with its left parent.

**Theorem 1 (strips).** Evolve only the columns $-w, \dots, w'$ from the single black cell, with every cell outside held
white. If $0 \le w < w'$ ($w' = \infty$ allowed), the strip's center equals $c(t)$ for $t \le 2w + 1$ and differs from it
at $t = 2w + 2$. So a strip with $w < w'$ that is correct at every time up to $n$ has $w \ge (n - 1)/2$ and width at
least $n$, and simulating it costs order $n^2$ cell updates.

*Proof.* Call a cell wrong when the strip and the true evolution differ there. The true column $-w - 1$ is white
before time $w + 1$ and black at time $w + 1$ (the left edge of the pattern is always black, since its neighborhood is
$0, 0, 1$); the true column $w' + 1$ is white before time $w' + 1$. A cell is wrong only if a parent is wrong or it is a
held cell, so by induction the wrong cells at time $t$ lie in columns at most $t - 2w - 2$ or at least $2w' + 2 - t$.
For $t \le 2w + 1$ column 0 is in neither range, since $2w' + 2 - t \ge 2(w' - w) + 1 \ge 3$. For the left range the
largest wrong column is exactly $t - 2w - 2$ for $w + 1 \le t \le 2w + 2$: at $t = w + 1$ it is the held column, and if
column $f$ is the largest wrong one at time $t$, then $x(t + 1, f + 1)$ reads $f$, which is wrong, and $f + 1$, $f + 2$,
which are right as long as $f + 2 < 2w' + 2 - t$, that is $t < w + w' + 1$, which holds for $t \le 2w + 1$; by
left-permutivity $x(t + 1, f + 1)$ is wrong. At $t = 2w + 2$ that is column 0.

The proof uses only left-permutivity and a black left edge, so it holds verbatim for Rules 90 and 150, which are
permutive in both neighbors; the computation confirms it for Rules 30, 90 and 150 and all $w \le 150$, with $w' = w + 1$
and with $w' = \infty$. For symmetric strips ($w' = w$) Rule 30's first error is at $2w + 2$ for every $w \le 150$ but
$w = 3$ (at time 9), while Rules 90 and 150 never err there, the two errors cancelling by linearity. With the left side
exact, a right side of width $w'$ alone first errs at a time between $4.13 w'$ and $6.52 w'$ for Rule 30
($25 \le w' \le 300$, every 25th width), and at exactly $2w' + 2$ for Rule 90: errors travel right at speed 1 and left
at a speed of about a quarter in Rule 30 (a heuristic reading of the ratios, which fluctuate).

**Theorem 2 (forward certificates).** Call the cells of row 0 and the cells outside the light cone of the seed, which are
white, free. A forward certificate of $c(n)$ is a set $S$ of cells, containing $(n, 0)$, such that every cell of $S$ at
time $s \ge 1$ has its left parent in $S$ or free, and has a black one of its two other parents in $S$ or free or, if
both are white, both of them; checking $S$ in order of time computes $c(n)$ with $|S|$ applications of the rule, and
every algorithm that obtains cells only by applying the rule forward, even one that skips a parent the OR does not
need, derives such a set. For Rule 30 every forward certificate has at least
$$\sum_{s = \lceil n/2 \rceil}^{n} (n - s + 1) = \frac{(\lfloor n/2 \rfloor + 1)(\lfloor n/2 \rfloor + 2)}{2}$$
cells, about $n^2/8$.

*Proof.* The cells that the conditions force from $(n, 0)$ form a certificate inside $S$ whose row $s$, $S_s$, lies in
$[-(n - s), n - s]$, so take $S$ of that form. Let $s \ge n/2 + 1$. Every $j \in S_s$ has $j - 1 \ge -(s - 1)$, so its
left parent is in the cone and not free, and $S_{s-1} \supseteq S_s - 1$. The largest $b \in S_s$ has
$b \le n - s \le s - 2$, so both of its other parents $(s - 1, b)$ and $(s - 1, b + 1)$ are in the cone and not free;
one of them is in $S$, and both exceed $b - 1 = \max(S_s - 1)$. So $|S_{s-1}| \ge |S_s| + 1$, and from $|S_n| \ge 1$, $|S_s| \ge n - s + 1$ for
$\lceil n/2 \rceil \le s \le n$.

The least certificate, found by integer programming (`scipy.optimize.milp`) for even $n \le 64$ and checked against
an exhaustive search over the choices of black parents for $n \le 9$ and against all subsets for $n \le 3$, has
between $0.413 n^2$ and $0.51 n^2$ cells for $16 \le n \le 64$. The memoized evaluation that skips the right parent
when the center parent is black derives at most six cells more for even $n \le 64$, and $0.415 n^2$ cells at
$n = 800$: short-circuiting the OR saves about a sixth of the $n^2/2$ cells of the dependency cone, and the bound
$n^2/8$ is a factor of about 3.3 below what is achieved. For Rule 90 both outer parents are always needed, the certificate is
forced, and it has $\sum_{s=1}^{n} \#\{ j : |j| \le \min(s, n - s),\ j \equiv n - s \pmod 2 \}$ cells, $0.251 n^2$ at
$n = 800$: a quadratic bound for a function that is 0 at every $n \ge 1$.

## What it means

Restricted models split in two. A model that reads the digits of $n$ arithmetically makes eventually periodic sequences
cheap, so a lower bound there that exceeds the cost of reading the digits by an unbounded amount is Problem 1 or harder.
Below that the rungs are statements about dyadic progressions: unbounded one-tape time is Problem 1 for power-of-two
periods, and time $\lfloor \log_2 n \rfloor + 2$ everywhere says that no progression $\{n + i\,2^{\ell(n)}\}$ is
constant; their finite checks are cheap (the tables above) but no argument reaches every $k$. A
model confined to the spacetime diagram gets bounds for every $n$ from the light cone and left-permutivity, which Rule 90
shares, so they say that simulation is quadratic, not that $c$ is hard; Problem 3 asks about algorithms that may leave
the diagram, as the linear-operation algorithm on a random-access machine does ([the barrier](problem-three-barrier.md)).
A new lower bound for $c$ itself would need a model that sees the digits of $n$ and still has to use the rule, and no
such model was found. The bounds of [cone screening](../../findings/complexity/cone-screening.md) are of the second kind
for an arbitrary row.

**What would change this.** A proof, for every $k$, that $c(m) \ne c(m + 2^k)$ for some $m \ge 2^{k-1}$ (the first rung;
it is Problem 1 for the periods $2^a$, which include the open least periods 2 and 4 of [the roadmap](../../ROADMAP.md)); or a model between the two
families, for example machines that receive $n$ in binary but may query the spacetime diagram only through the rule,
in which periodicity of $c$ would not help.

**Reproduce.**

```bash
python -m computations.restricted_models --max-w 150 --right-max 300 --max-cert 64 --max-lazy 800 --max-k 20
```

It takes about ten minutes, nearly all of it to compute the first $3 \cdot 2^{19} + 64$ cells of $c$; with the default
`--max-k 16` it takes seconds. `tests/test_restricted_models.py` checks the strip evolution against a cell-by-cell
evolution from the rule number, Theorem 1 for $w < 30$, the certificate minima against exhaustive searches, the Rule 90
closure for minimality, and the dyadic offsets and ray counts against direct scans.
