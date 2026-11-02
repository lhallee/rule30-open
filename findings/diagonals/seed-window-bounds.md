---
title: A sound abstraction of the seed rows by a window of times before the onset front gives T_j at most ceil(3j/2) + 5 for every seed and every j up to 1,252, at most ceil(8j/5) up to 87,866, and the exact latest onset to depth 88; the bound's slope falls from 2.03 to about 1.52 as the window grows from 0 to 8 times
category: diagonals
problems: [2]
status: computed
formalization: wanted
evidence: [computations/seed_certificate.py]
---

# A sound abstraction of the seed rows by a window of times before the onset front gives T_j at most ceil(3j/2) + 5 for every seed and every j up to 1,252, at most ceil(8j/5) up to 87,866, and the exact latest onset to depth 88; the bound's slope falls from 2.03 to about 1.52 as the window grows from 0 to 8 times

A *seed* is a row white left of a black cell $lo$, with any cells $x_1, x_2, \dots$ right of it. Its left diagonals
$D_j(t) = \mathrm{cell}_t(lo - t + j)$ follow $D_{j+2}(t+1) = D_j(t) \oplus (D_{j+1}(t) \lor D_{j+2}(t))$ with
$D_0 = 1$, $D_{-1} = D_{-2} = 0$ and $D_j(0) = x_j$; $T_j$ is the onset of $D_j$ and $M_j$ the largest onset over all
seeds ([seed-uniform onsets](seed-uniform-onsets.md)). Write $R_j = \max(T_0, \dots, T_j)$ for the *front*. Since
$\lceil 3j/2 \rceil$ is nondecreasing, $T_i \le \lceil 3i/2 \rceil + c$ for every $i \le j$ is the same as
$R_j \le \lceil 3j/2 \rceil + c$. The conjecture there, $M_j \le \lceil 3j/2 \rceil + 5$ for every $j$, was known for
$j \le 76$.

## Result

**The window abstraction.** Fix a width $h$ and a period $P$. The abstract state of a seed at depth $j$ is

- the *periodic word*: the pair $(D_{j-1}, D_j)$ at the times $R_j, \dots, R_j + P - 1$;
- the *age* $a = \min(R_j, h)$;
- the *window*: the pair at the times $R_j - a, \dots, R_j - 1$.

The step to depth $j + 1$ forgets everything but the state and the one cell $D_{j+1}(R_j - a)$, which it leaves free:
two transitions per state. The values $U_j$ (a bound on $R_j$) and $V_j$ (a bound on $T_j$) are the largest over the
abstract paths of length $j$ from the state at depth 0. The abstraction is *sound*: every seed's state at every depth
is an abstract state, and its step is one of the two transitions, so $R_j \le U_j$ and $T_j \le V_j$ for every seed.
With $P = 16$, every transition met to the depths below keeps period 16, which the program checks at each step.

| Window $h$ | 0 | 2 | 4 | 6 | 8 |
|---|---:|---:|---:|---:|---:|
| Slope of $U_j$ on depths 200 to 398 | 2.025 | 1.753 | 1.626 | 1.556 | 1.515 |
| Largest $V_j - \lceil 3j/2 \rceil$, $j \le 398$ | 186 | 58 | 18 | 10 | 5 |
| Abstract states at a depth, at most | 8 | 128 | 2,048 | 32,768 | 524,288 |

- **$h = 8$.** $V_j \le \lceil 3j/2 \rceil + 5$ for every $j \le 1{,}252$, so **every seed has
  $T_j \le \lceil 3j/2 \rceil + 5$ for $j \le 1{,}252$**; at $j = 1{,}253$ the bound is
  $\lceil 3j/2 \rceil + 6$. Past that the excess grows: it is at most 50 to depth 4,000 and 305 to depth 13,541, where the run was
  stopped, with $V_j \le \lceil 31j/20 \rceil + 2$ and $V_j \le \lceil 8j/5 \rceil$ throughout; the slope of $U_j$ is
  1.516 on depths 1,000 to 4,000 and 1.524 on 10,000 to 13,541.
- **$h = 6$.** Run to depth 87,866 (the last depth before the single cell's period becomes 32), with every
  transition keeping period 16: $V_j \le \lceil 8j/5 \rceil$ for every $j \le 87{,}866$, so **every seed has
  $T_j \le \lceil 8j/5 \rceil$ for $j \le 87{,}866$**, and also $V_j \le \lceil 39j/25 \rceil + 16$. The slope of
  $U_j$ is 1.53 to 1.57 on each of the ranges cut at depths 400, 1,000, 4,000, 10,000, 20,000, 40,000, 53,207,
  58,286 and 87,866 (1.554 on the last), and 1.48 to 1.63 on stretches of 2,000 depths, and the excess over
  $\lceil 3j/2 \rceil$ reaches 4,797. The abstract states number at most 262,144 at a depth: the periodic words at a
  depth number 16 from depth 400, 32 from 53,208 and 48 from 58,287 (after the white diagonals) and 64 from 72,576.
- **The exact maxima.** For $h = 8$, $V_j = M_j$ at every $j \le 76$ but $j = 73$ ($V_{73} = 107$, $M_{73} = 105$).
  At $j = 77, \dots, 88$, 90, 92, 105, 107 to 115 and 117 the bound $V_j$ is the onset of the seed with $x_3 = 1$
  (black cells at $lo$ and $lo + 3$), so there $M_j = V_j$, the single cell's onset plus 6:

| $j$ | 77 | 78 | 79 | 80 | 81 | 82 | 83 | 84 | 85 | 86 | 87 | 88 | 90 | 92 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $M_j$ | 114 | 113 | 117 | 116 | 121 | 119 | 123 | 122 | 131 | 125 | 133 | 133 | 133 | 133 |
| $M_j - \lceil 3j/2 \rceil$ | $-2$ | $-4$ | $-2$ | $-4$ | $-1$ | $-4$ | $-2$ | $-4$ | 3 | $-4$ | 2 | 1 | $-2$ | $-5$ |

  and $M_j$ = 153, 157, 155, 159, 160, 161, 162, 164, 164, 168, 170 at $j$ = 105, 107, ..., 115, 117. So the worst
  seed stays the delayed single cell of [seed-uniform onsets](seed-uniform-onsets.md) on all these depths.
- **How loose.** A beam search over seeds (256 rows kept per depth by latest pair onset, `driven_beam` from the pair
  (white, black)) finds seeds later than the seed $x_3 = 1$ at depths 3, 8, 10 and 12, and past them first at depth
  159 and at many depths after it, by up to 53 below depth 1,000, but the latest onset it finds stays within 43 of the single cell's, at least 36 below $\lceil 3j/2 \rceil$ from depth 200 on and
  at least 177 below it from depth 900 on (1.313 per depth at depth 1,000). Meanwhile $V_j$ stays between
  $\lceil 3j/2 \rceil - 30$ and $\lceil 3j/2 \rceil + 2$ on depths 100 to 1,000 (1.489 per depth at 1,000). The bound
  exceeds every seed found by up to 38 on depths 100 to 199 and by up to 178 below depth 1,000: the slope near $3/2$
  is the abstraction's, and the latest onsets found grow like the single cell's.

## Why the abstraction is sound

1. **The pair repeats from the front.** $T_{j-1}, T_j \le R_j$, so from $R_j$ on the pair repeats with its period,
   and with $P$ when $P$ is a multiple of it. Its values on $[R_j, \infty)$ are the periodic word read with period
   $P$.
2. **The next diagonal from one cell.** $D_{j+1}(t + 1)$ is a function of $D_{j-1}(t)$, $D_j(t)$ and $D_{j+1}(t)$, so
   from $D_{j+1}(R_j - a)$ and the pair on $[R_j - a, \infty)$, the state gives $D_{j+1}$ on $[R_j - a, \infty)$. When
   $a < h$ the age is $R_j$ itself, the window starts at time 0, and the free cell is $x_{j+1}$: the step is exact.
3. **The increment.** If $D_j$ has a black cell $r$ in $[R_j, R_j + P)$, then $D_{j+1}(r + 1) = \lnot D_{j-1}(r)$ at both
   $r$ and $r + P$, and from there both sides follow the same periodic pair, so $D_{j+1}$ repeats with period $P$
   from $r + 1$ (the reset of `D_periodic_of_black` in [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)). If
   $D_j$ is white on a whole period, $D_{j+1}(t + P) \oplus D_{j+1}(t)$ is constant from $R_j$
   (`agree_or_flip_of_white` of [PrefixWalk](../../Rule30Open/Diagonals/PrefixWalk.md)). Either way the last
   $u < 2P$ with $D_{j+1}(R_j + u) \ne D_{j+1}(R_j + u + P)$ decides everything: none at $u \ge P$ means period $P$
   (otherwise the program stops), and $T_{j+1} = R_j + u + 1$, or $T_{j+1} \le R_j$ if there is none. So
   $R_{j+1} - R_j$ is read exactly, and so is $T_{j+1}$ when its last change falls in the window; otherwise
   $T_{j+1} \le R_j - a$.
4. **The new state.** The new pair $(D_j, D_{j+1})$ is known on $[R_j - a, \infty)$, which contains the new window
   and periodic word; it repeats with period $P$ from $R_{j+1}$ by step 3. By induction on $j$, every seed's state is
   an abstract state with period $P$ as long as no abstract transition leaves period $P$. Two abstract paths that
   reach the same state have the same future, so keeping the largest front per state loses nothing.

No property of the single cell's skeleton is used: the period is checked, not assumed. That a table read with period
$P$ gives the true onsets is the window argument of [seed-uniform onsets](seed-uniform-onsets.md).

## What it does not give

The abstract states at depth $j$ carry the periodic word of depth $j$, and the periodic pairs of the single cell never
repeat up to a time shift (lead 3 of [linear settling leads](../../negative-results/diagonals/linear-settling-leads.md)).
So the computation is a certificate for each depth separately, not a finite certificate for every $j$; why no finite
one exists without a new fact about the settled side is in
[seed finite certificate](../../negative-results/diagonals/seed-finite-certificate.md). The bound grows with the
period too: the program needs $P = 16$ from depth 399, and the single cell's period is 32 from depth 87,867.

## Method

- `window_bounds` (numpy) and `seed_certificate_window.c` (dense arrays indexed by word, age and window, eight times
  per table step) run the abstraction depth by depth; they agree on every bound, onset bound and state count at
  depths to 398 for $h = 0, 3, 6$ and on the tests.
- **Checks** (`tests/test_seed_certificate.py`): with $h = 16$ every seed of 10 cells is followed exactly, and the
  bounds equal the maxima of the onset table of `seed_onsets`; with $h = 2, 4$ the state that a direct run assigns to
  every seventh seed of 10 cells is among the abstract states with a front at least its own; with $h = 5$ the onset
  bounds are at least the exact $M_j$ of the branch and bound for $j \le 76$ and equal to them for $j \le 48$.

## Reproduce

```bash
python -m computations.seed_certificate --window 398 --widths 0,2,4,6,8   # the table, about 30 s
python -m computations.seed_certificate --seeds 1000 --beam-width 256    # exact M_j past 76, about 3 min
python -m computations.seed_certificate --window 87866 --widths 6        # about 21 min, one thread
python -m computations.seed_certificate --window 13541 --widths 8        # about 45 min on two threads
```
