---
title: After a period doubling to period 2p the next white diagonal comes m(p) depths later; m(p) is computed for p up to 16, exceeds 49 for every p but 1, 2 and 5, grows like a minimum of fair waiting times, and no structured family of start words gives short gaps to p = 40
category: diagonals
problems: [2]
status: computed
formalization: partial
evidence: [computations/doubling_gaps.py]
---

# After a period doubling to period 2p the next white diagonal comes m(p) depths later; m(p) is computed for p up to 16, exceeds 49 for every p but 1, 2 and 5, grows like a minimum of fair waiting times, and no structured family of start words gives short gaps to p = 40

The periods of the single cell's left diagonals $D_j(t) = \mathrm{cell}(t, j - t)$ grow only by doubling, right after
an eventually white diagonal $w$ whose predecessor $D_{w-1}$ has odd weight per period
([LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)). Then $Y = D_{w+1}$ is anti-periodic,
$Y(t + p) = \lnot Y(t)$, of period $P = 2p$, and the settled words that follow are the orbit of the pair map
$F(A, B) = (B, C)$ of [settled words](settled-words.md) from $(0, Y)$ to the first pair $(X, 0)$ whose second word is
white. Its length, the *gap*, is the number of depths to the next white diagonal. Let $m(p)$ be the least gap over
every anti-periodic $Y$ of least period $2p$. A bound $m(p) \ge f(p)$ for every $p$ would bound the periods: the
doublings below depth $j$ would number at most about $f^{-1}(j)$, so $m(p) \ge 2^{cp}$ would give $P_j = O(\log j)$
and $m(p) \ge cp$ would give $P_j = O(j)$, against the kit main branch's $P_j \le 2^{\lfloor (j+5)/6 \rfloor}$
(`Rule30LeftAntiPeriod.D_evPer_pow_div_six`).

## The census (computed, $p \le 16$)

`census` walks the orbit of every rotation class of anti-periodic words of least period $2p$ (the gap does not depend
on the rotation, since $F$ commutes with it) in lockstep up to $10^7$ steps. The column "reached" counts the classes
whose orbit ends within the cap; "heuristic" is the number expected if each step of a fair pair of words of period
$2p$ ended the orbit with probability $2^{-2p}$, the chance that a fair word of $2p$ bits is white; the last column is
$m(p) \cdot n / 4^p$, which under that heuristic is the minimum of $n$ waiting times scaled by their mean over $n$, a
variable of mean 1.

| $p$ | classes $n$ | $m(p)$ | minimizer (hex, least rotation) | least odd gap | least even gap | reached | heuristic | $m(p)\, n / 4^p$ |
|---:|---:|---:|---|---:|---:|---:|---:|---:|
| 1 | 1 | 5 | 1 | 5 | - | 1 | 1.0 | 1.250 |
| 2 | 1 | 21 | 3 | 21 | - | 1 | 1.0 | 1.312 |
| 3 | 1 | 56 | 7 | - | 56 | 1 | 1.0 | 0.875 |
| 4 | 2 | 88 | f | 371 | 88 | 2 | 2.0 | 0.688 |
| 5 | 3 | 23 | 1f | 23 | 224 | 3 | 3.0 | 0.067 |
| 6 | 5 | 98 | 3f | 1,585 | 98 | 5 | 5.0 | 0.120 |
| 7 | 9 | 1,247 | 477 | 1,247 | 37,348 | 9 | 9.0 | 0.685 |
| 8 | 16 | 6,343 | 14eb | 6,343 | 18,826 | 16 | 16.0 | 1.549 |
| 9 | 28 | 8,785 | 1df1 | 8,785 | 10,168 | 28 | 28.0 | 0.938 |
| 10 | 51 | 6,754 | 15ba9 | 20,425 | 6,754 | 51 | 51.0 | 0.328 |
| 11 | 93 | 48,180 | 177d1 | 208,871 | 48,180 | 88 | 84.4 | 1.068 |
| 12 | 170 | 49,231 | 2b4d4b | 49,231 | 156,998 | 83 | 76.3 | 0.499 |
| 13 | 315 | 5,808 | 75fc5 | 160,585 | 5,808 | 40 | 43.6 | 0.027 |
| 14 | 585 | 42,282 | 1aa3957 | 145,891 | 42,282 | 18 | 21.4 | 0.092 |
| 15 | 1,091 | 429,545 | 51575d5 | 429,545 | 4,773,068 | 9 | 10.1 | 0.436 |
| 16 | 2,048 | 414,989 | 1632e9cd | 414,989 | - | 2 | 4.8 | 0.198 |

A dash means no class of that parity ends within the cap. The minimizer is $1^p 0^p$ (hex $2^p - 1$) for $p \le 6$
and an irregular word from $p = 7$ on. $m$ is not monotone ($m(5) = 23 < m(4)$, $m(13) = 5{,}808$), and the counts of
orbits that end within the cap follow the fair-word heuristic at every $p$ (within 1.3 standard deviations of a
binomial count, the largest departures 88 against 84.4 and 2 against 4.8). Under that heuristic, which is a model and
not a property of the pair map, $m(p)$ is about $4^p / n \approx 2p \cdot 2^p$ times a variable of mean 1, and the
chance that $m(p) < 7p$ is about $3.5 \cdot 2^{-p}$, summable over $p$. The values $m(1), \dots, m(4)$ are proved in
Lean, and for the single cell's half-periods $p = 1, 2, 4$ the bound on its diagonals
(`D_doubling_gap` of [DoublingGaps](../../Rule30Open/Diagonals/DoublingGaps.md)).

## The single cell's own words (computed)

`single_cell` reads the white diagonals of the single cell below depth 87,870 from the last 128 of 150,000 steps, and
runs the pair map from each one's own $D_{w+1}$. The model gives every gap of the run, the three that keep the period
included:

| White $w$ | weight of $D_{w-1}$ | period after $w$ | $D_{w+1}$ (hex) | next white | gap of the run | gap of the model |
|---:|---:|---:|---|---:|---:|---:|
| 2 | 1 | 2 | 2 | 7 | 5 | 5 |
| 7 | 1 | 4 | 3 | 28 | 21 | 21 |
| 28 | 3 | 8 | 4b | 399 | 371 | 371 |
| 399 | 3 | 16 | 9f60 | 53,207 | 52,808 | 52,808 |
| 53,207 | 6 | 16 | 3082 | 58,286 | 5,079 | 5,079 |
| 58,286 | 10 | 16 | b5a7 | 87,866 | 29,580 | 29,580 |
| 87,866 | 5 | 32 | 30cfcf30 | | | 1,420,791,102 |

So the gaps after the single cell's doublings are 5, 21, 371 and 52,808, against $m(p) = 5, 21, 88$ and 6,343 at
$p = 1, 2, 4, 8$. The last row is a computation of the model past the run: the orbit of $F$ from the cell's own
$D_{87{,}867}$ (period 32) ends after 1,420,791,102 steps, so **the next white diagonal of the single cell is at depth
1,420,878,968**, and $D_{w-1}$ there has weight 20, so it keeps the period 32. Behind it $D_{w+1}$ is one of two
complementary words, fixed by a bit of the transient that the pair map does not see
([LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md), `D_shift_of_white`); from one the next white diagonal is at
depth 3,340,408,059 (weight 16, the period stays 32), from the other at depth 2,107,985,254 (weight 17), where the
period doubles to 64. The heuristic of [left records](left-records.md) put the period-64 record near $2^{33}$. These
depths rest on the settled word of $D_{87{,}867}$ read from the run and on the pair map being exact on settled words,
which [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md) (`D_periodic_of_black`) proves; no diagonal past depth
200,000 has been evolved.

## Structured families (computed, the kill test)

`family_gaps` runs one orbit per family and $p \le 40$ (words of up to 80 bits), with a cap of $10^7$ steps. Each
family gives the first half of $Y$: the block $1^p$ ($Y = 1^p 0^p$; a half with one black cell gives a rotation of
it), alternating blocks $(1^k 0^k)^*$ for $k = 1, 2, 3$, the $p = 5$ minimizer's half $1^5 0^5$ repeated ($k = 5$),
the $p = 7$ minimizer's half repeated, two black cells at $0$ and $\lfloor p/2 \rfloor$, Thue-Morse, and a random half
(seeded, a control). A family is skipped at the $p$ where its word has least period below $2p$.

| $p$ | block | alt 1 | alt 2 | alt 3 | alt 5 | $p = 7$ half | two cells | Thue-Morse | random |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 88 | 371 | 88 | 88 | 88 | 88 | 371 | 371 | 371 |
| 5 | 23 | | 691 | 23 | 23 | 224 | 224 | 691 | 23 |
| 6 | 98 | 6,070 | | 98 | 98 | 1,560 | 1,585 | 6,070 | 1,997 |
| 7 | 15,847 | | 25,525 | 1,247 | 15,847 | 1,247 | 41,490 | 2,543 | 15,847 |
| 8 | 49,732 | 93,358 | 40,804 | 62,791 | 49,732 | 29,167 | 29,167 | 171,541 | 125,209 |
| 9 | 144,276 | | 490,344 | | 144,276 | 368,181 | 368,181 | 15,064 | 194,336 |
| 10 | 1,890,520 | 1,200,626 | | 137,411 | 1,890,520 | 2,578,536 | 1,037,638 | 3,137,869 | 416,564 |
| 11 | 404,459 | | 915,245 | 2,295,505 | 3,351,469 | 7,633,028 | 7,633,028 | 911,254 | 1,001,437 |
| 12 | $> 10^7$ | 7,499,482 | $> 10^7$ | $> 10^7$ | $> 10^7$ | $> 10^7$ | $> 10^7$ | $> 10^7$ | $> 10^7$ |
| 13 | $> 10^7$ | | $> 10^7$ | 5,104,809 | 9,464,094 | $> 10^7$ | $> 10^7$ | $> 10^7$ | $> 10^7$ |

For $p = 1, 2, 3$ there is one class and every family gives $m(p)$. From $p = 14$ to 40 every family word that has
least period $2p$ runs past $10^7$ steps. So **no family has a gap below $7p$ for any $6 \le p \le 40$**, and none
looks linear: the family gaps grow like those of the random control, about $4^p$ in order of magnitude. The kill test
of a linear family fails at every family tried, and so does the test of $m(p) < 7p$ on the census to $p = 16$.

## Short gaps for every $p$: the sink words lie in a shift of finite type (paper and computation)

Read the regime backward from its sink $(X, 0)$: with $E_0 = 0$, $E_1 = X$ and
$E_{i+2}(t) = E_i(t+1) \oplus (E_{i+1}(t) \lor E_i(t))$ (the step solved backward), $E_i = D_{w'-i}$. Each $E_i$ is a
local rule applied to $X$: $E_i(t)$ reads $X(t), \dots, X(t + r_i)$ with $r_i = \lfloor (i-1)/2 \rfloor$, and for odd
$i$ it is $X(t + r_i)$ XOR a function of the cells before it, by induction on $i$ (`backward_words`,
`permutive_check`). If the regime that ends at $w'$ starts at the white diagonal $w = w' - g$, then $E_g$ is white
and $E_{g-1} = Y$ is not; on periodic words $E_g$ is white exactly when $E_{g-2}$ is all black (behind a white diagonal
the next but one is black, and a black $D_{w+2}$ makes $D_w(t) = D_{w+2}(t+1) \oplus 1 = 0$). The converse fails: a
word $X$ with $E_{g-2}$ all black can have a white $E_i$ for some $0 < i < g$, and then $g$ spans two regimes. So the
words below describe a set that contains the sink words of the regimes with gap $g$, which is the direction the
lower bounds need.

- **Odd gaps (paper).** For odd $g$, $E_{g-2}$ is right-permutive of radius $(g-3)/2$, so $E_{g-2} = 1$ fixes each
  cell of $X$ from the $(g-3)/2$ before it. A periodic $X$ is then a cycle of a map on $2^{(g-3)/2}$ windows, and its
  least period, which is the regime's period, is at most $2^{(g-3)/2}$. So **a regime of least period $q$ that ends
  at an odd distance $g$ has $g \ge 2 \log_2 q + 3$**, for every start word, doubling or not.
- **Every gap up to 49 (computation).** For each $g$, `source_graph` builds the shift of finite type of the
  bi-infinite $X$ with $E_{g-2}$ all black, trimmed to the windows on bi-infinite paths, and the two-track graph of the
  pairs $(X, X')$, $X' = \mathrm{rot}_p X$, of such words with $E_{g-1}(X') = \lnot E_{g-1}(X)$ at every time: an
  anti-periodic source of half-period $p$ with gap $g$ is a walk in it that comes back swapped after $p$ steps. In a
  single regime $X$ has the least period $2p$ of $Y$ (the pair map commutes with rotation, and $Y$ is a local function
  of $X$), so where that graph is a union of disjoint cycles, $2p$ is one of their lengths.

| $g$ | 5 | 6 | 7 | 8 | 11 | 15 | 21 | 23 | 25 | 26 | 31 | 33 | 39 | 47 | 49 |
|---:|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| one-track cycles | 2 | none | 4 | branches | 11 | 20 | 4, 4, 8, 10 | 10, 12 | 9, 10, 18 | 4 | 20, 34 | 5, 6, 13, 79 | 7, 14, 17, 20, 143 | 5, 7, 18, 21, 99, 198, 237 | 4, 7, 22, 24, 32, 47, 56, 62 |
| two-track cycles ($2p$) | 2 | none | none | none | none | none | 4 | 10 | none | 4, 4 | none | none | none | none | none |

For every $5 \le g \le 49$ the two-track graph is a union of disjoint cycles, nonempty only at $g = 5$, 21, 23 and 26,
with lengths 2, 4 and 10. The cycles at $g = 26$ span two regimes and are not a regime of half-period 2 (the only
class at $p = 2$ has gap 21): their $X$ has period 4 and their $Y = E_{25}$ has least period 2, a regime of gap 5
from $Y$, then a doubling white diagonal, then a regime of gap 21; a search of every $X$ of least period at most 16
finds the same. So **$m(p) > 49$ for every $p$ other than 1, 2 and 5**, a bound for all $p$ from finitely
many finite graphs. The one-track graph branches at $g = 8, 14, 16, 32, 44, 48$, where its words have arbitrarily
large least periods, so the odd-gap argument has no analog for every even gap; it is empty at $g = 6, 10, 18, 22, 34$: no regime
of any period, and so no two consecutive white diagonals of the single cell, is 6, 10, 18, 22 or 34 depths long. The
graphs of $g = 49$ have $2^{24}$ windows; the method costs $2^{g/2}$ and stops near there in 4 GB.

For the single cell, whose half-periods are powers of two, each doubling at half-period $p \ge 8$ is therefore
followed by more than 49 depths before the next white diagonal. With the first doubling at depth 2 and the Lean values
$5, 21, 88$ for $p = 1, 2, 4$, the $k$-th doubling white diagonal lies at depth at least $116 + 50(k - 4)$ for
$k \ge 4$, so by this computation $P_j \le 2^{4 + (j - 117)/50}$ for $j \ge 117$, against the kit main branch's
$2^{\lfloor (j+5)/6 \rfloor}$. A bound of this kind for every $g$ is what a growing $f$
would need, and the computation reaches only a constant.

## Mechanism: the half-period damage (computed; heuristic reading)

Along a regime of period $2p$ let $h_j = D_j \oplus \mathrm{rot}_p(D_j)$; $h_j = 0$ exactly when $D_j$ has period $p$.
$h$ is all black at $Y$ and at $D_{w+3}$, white at $D_{w+2}$ (all black) and at the end, and never white at two
consecutive depths (two consecutive words of period $p$ would give period $p$ to every word before them, the kit main
branch's `D_evPer_pair_iff_all`). On the minimizing orbits of $p = 5, \dots, 12$ (`half_damage`):

| $p$ | gap | depths with $h_j = 0$ | their fraction | $2^{-p}$ | mean weight of $h_j$ over $2p$ |
|---:|---:|---:|---:|---:|---:|
| 5 | 23 | 3 | 0.13 | 0.031 | 0.567 |
| 6 | 98 | 3 | 0.031 | 0.016 | 0.495 |
| 7 | 1,247 | 27 | 0.022 | 0.0078 | 0.482 |
| 8 | 6,343 | 24 | 0.0038 | 0.0039 | 0.499 |
| 9 | 8,785 | 22 | 0.0025 | 0.0020 | 0.502 |
| 10 | 6,754 | 4 | 0.0006 | 0.0010 | 0.503 |
| 11 | 48,180 | 26 | 0.0005 | 0.0005 | 0.499 |
| 12 | 49,231 | 10 | 0.0002 | 0.0002 | 0.499 |

The damage behaves like a symmetric fair word: its weight sits at $p$, it vanishes at a rate near $2^{-p}$, and its
weight just before the white diagonal is not small (16 of 18 at $p = 9$, 12 of 20 at $p = 10$). No monotone integer
quantity along the orbit appears in it, its runs or its parity; the reading that the regime is a fair waiting time is
a heuristic.

## What it means

The question is whether the gap after a doubling can be bounded below uniformly in the start word, by a function
that grows. The kill tests both fail: no structured family gives gaps below $7p$ for $6 \le p \le 40$, the census
gives $m(p) \ge 21$ for $2 \le p \le 16$, and the source graphs give $m(p) > 49$ for every $p \notin \{1, 2, 5\}$.
But nothing here grows with $p$ for every $p$: the census stops at $p = 16$, the source graphs at $g = 49$, the
odd-gap bound $2 \log_2 q + 3$ does not cover even gaps (the one-track graphs branch at even $g$), and the damage shows
no potential. The data fit $m(p) \approx 2p \cdot 2^p$ times a random factor, which would give $P_j = O(\log j)$; a
proof would need the two-track graphs to stay unions of short cycles for every $g$, a statement about the backward
pair map as hard as the fair-word behavior it would explain.

## Reproduce

```bash
python -m computations.doubling_gaps --census 1-16 --cap 10000000   # the census, about 5 min, 1 thread
python -m computations.doubling_gaps --families 40 --cap 10000000   # the families, about 3 min
python -m computations.doubling_gaps --single-cell --cap 100000     # the single cell's regimes, about 10 s
python -m computations.doubling_gaps --predict --cap 274877906944   # past depth 87,866, about 1 min
python -m computations.doubling_gaps --sources 5-49                 # the source graphs, about 3 min, 3.6 GB
python -m computations.doubling_gaps --damage 5-12 --cap 60000      # the half damage on the minimizing orbits
```

`tests/test_doubling_gaps.py` checks $m(1), m(2), m(3)$ against the diagonal recursion run cell by cell, the C program
against numpy, the white-step identity on sinks built backward and on forward words, the radius and permutivity of
the backward words, the single cell's first regimes against a Rule 30 run, the source graphs against every regime of
period at most 10 with gap at most 24, and the words behind a white diagonal.
