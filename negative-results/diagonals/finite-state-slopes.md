---
title: A finite automaton over the center column certifies no slope for black runs of the driven left half unless those runs are bounded
category: diagonals
problems: [2]
status: negative
kind: barrier
evidence: [computations/constrained_runs.py]
---

# A finite automaton over the center column certifies no slope for black runs of the driven left half unless those runs are bounded

**Question.** The [driven-runs conjecture](../../findings/diagonals/driven-left-runs.md) bounds the black run of
column 0 from time $a$ that a left half driven from a white start allows. One constraint needs no right half: since
$c(t + 1) = x_{-1}(t) \oplus (c(t) \lor x_1(t))$, a black center fixes the next one, $c(t + 1) = \lnot x_{-1}(t)$ when
$c(t) = 1$. Call a driver word $c(0) = 1, c(1), \ldots, c(n - 1)$ *admissible* when it obeys this at every step; the
single cell's center column is admissible. Could a finite-state object prove the conjecture's black half: a finite
automaton reading the driver that accepts every admissible word and in whose accepted words a black run from time $a$
has length at most $\beta a + C$ with $\beta < 3/5$? Three forms were tested: the exact language, every outer automaton
on a fixed window of cells, and the 2-adic reading of a black run.

**Outcome.** None works. The first item is a proof that a finite automaton bounds the black runs only if the
admissible black runs are bounded; the other three are computations on the stated ranges.

- **Pumping.** Let an automaton with $q$ states, deterministic or not, accept every admissible word. If some admissible
  word $u 1^m$ has $m \ge q$, the accepting path of $u 1^m$ repeats a state while it reads the 1s, at a loop $1^p$ with
  $1 \le p \le q$, so the automaton accepts $u 1^{m + jp}$ for every $j$: a black run from time $|u|$ with no bound at
  all. Admissible words with a black run of 21 from time 145 and from time 150 exist (`constrained_runs table`, below),
  so every such certificate has more than 21 states, and if admissible black runs are unbounded, as the growth of the
  longest one along $t \le 150$ suggests, no finite automaton certifies any bound, of slope $\beta$ or otherwise. The
  white half is outside this question altogether: a white center leaves the next one free, so the admissible words
  contain $0^m$ after every prefix that ends in 0, and the white bound $R_W$ of the conjecture comes from column 1, not
  from the driver.
- **The exact language needs about $2^k$ states at resolution $k$.** The future of length $k$ of a reachable state
  (left half at $t$, $c(t)$) depends only on $c(t)$ and the cells $-1 .. -k$, since the constraint at time $t + j$ reads
  cell $-1$ at time $t + j$. Over every reachable state with $t \le 60$, every one of the $2^{k + 1}$ pairs (window of
  $k$ cells, $c$) occurs for $k \le 10$ (4,095 of 4,096 at $k = 11$, 8,095 of 8,192 at $k = 12$), and the number of
  distinct sets of admissible futures of length $k$ is exactly $2^k + 1$ for $k = 2, \ldots, 11$ (5, 9, 17, ..., 2,049)
  and 4,093 at $k = 12$ (`constrained_runs classes`). Of them $2^{k - 1}$ belong to states with $c = 0$ for
  $k \le 11$ (2,045 at $k = 12$). The count follows from that: a state with $c = 1$ reads the single first letter
  $b = \lnot x_{-1}$ and moves to $(x', b)$, and $x \mapsto (b, x')$ on $k$ and $k - 1$ cells is a bijection by left
  permutivity, so while every window is reached the states with $c = 1$ have as many classes at $k$ as all states
  have at $k - 1$. Each distinct future set is a distinct residual of the language, so a deterministic automaton that
  accepts exactly the admissible words has at least 4,093 states, and the count doubles with each cell of resolution
  as far as it was computed.
- **Every fixed-window outer automaton admits a black run that never ends.** The outer automaton keeps the cells
  $-1 .. -w$ and the center, treats cell $-(w + 1)$ as free at each step, and keeps the constraint. Started from the
  white window with $c(0) = 1$, it admits within $n$ steps a black run of $n - 2$ ($w = 3, 4, 5$), $n - 5$ ($w = 6$),
  $n - 6$ ($w = 7, 8$) and $n - 7$ ($w = 9, 10$), at $n = 50, 100, 200$ (`constrained_runs window`). The reason is
  exact: for each $w = 3, \ldots, 10$ exactly one window keeps the center black forever, the alternating one (cell $-j$
  black exactly for even $j$), reached at time 3 ($w \le 5$), 6, 7, 7, 8 and 8. It is a fixed point for every $w$: with
  the free cell set to continue the pattern, one step with a black center reproduces it and keeps cell $-1$ white. It
  is reachable whenever some reachable left half alternates on $w$ cells, which holds for $w \le 20$ by the black runs
  of 21 above; the window game of [driven run slopes](driven-run-slopes.md) (route 3) is the same automaton without
  the constraint. So a fixed-window abstraction is weaker than the light cone ($L \le a + 1$), the same lesson as
  [fixed-depth strips](fixed-depth-strips.md): the depth a comparison uses has to grow in proportion to $a$.
- **The carry valuation restates the alternating domain.** Read the left half at $t$ as the integer $N_t$ with bit
  $k - 1$ the cell $-k$. Then the black run from $t$ is $v_2(3 N_t + 2) + 1$ at all 1,935 black times $t < 3{,}900$ of
  the single cell (`constrained_runs carry`). It is an identity, not a finding: $-2/3$ is the 2-adic integer whose bits
  read $0, 1, 0, 1, \ldots$ from bit 0, so $2^v$ divides $3 N + 2$ exactly when the low $v$ bits of $N$ alternate that
  way, which is the alternating right end that makes a black run (the finding's *black runs are alternating domains*).
  Bounding the valuation along the orbit is the original problem. The 2-adic reformulations of
  [reformulations](../dynamics/reformulations.md) (*thin image*, *virtual columns*) stop at the same point.

**What it means.** A certificate for the driven black runs has to carry information about the left half that grows
with $t$: an automaton of any fixed size, and in particular any fixed window, either rejects an admissible word or
bounds nothing. What remains is a description of the reachable set $\mathcal{L}_t$ itself, of size growing like
$2^{0.09 t}$ on the computed range, good enough to bound its alternating right ends; the
[finding](../../findings/diagonals/driven-left-runs.md#long-runs-against-fair-bits-a-heuristic) records how those right
ends compare with fair bits.

## Reproduce

```bash
python -m computations.constrained_runs table --steps 150 --every 5 --compare   # about 5 min
python -m computations.constrained_runs classes --steps 60 --kmax 12            # about 30 s
python -m computations.constrained_runs window --wmax 10                        # about 1 s
python -m computations.constrained_runs carry --steps 4000                      # about 1 s
```
