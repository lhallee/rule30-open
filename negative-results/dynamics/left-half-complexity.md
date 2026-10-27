---
title: Bounding the left half by the right channel needs Problem 1 itself
category: dynamics
problems: [1]
status: negative
kind: dead-end
---

# Bounding the left half by the right channel needs Problem 1 itself

**Idea.** Under an eventual period of the center, the left half is rebuilt from the center and from column 1 at the
center's white times (left permutivity). Column 1 is the right half's output, and under periodic drives it has low
complexity ([the one-way valve](../../findings/dynamics/one-way-valve.md)). So every left column would be a sliding
block code of a low-complexity sequence: for a period $P$, the subword complexity of column $-k$ is at most $P^2$ times
that of column 1 at the white times, at length $n + k$. The left half would have to be as tame as the right channel,
while every simulation shows it maximally complex.

**Why it stalls.** Turning the comparison into a contradiction needs a lower bound on the complexity of the driven
left half for every finite starting row: a statement that a specific deterministic orbit is chaotic, which is the
same kind of statement as Problem 1. For the words of period 4, whose right channel locks from every start tried,
masked Jen would exclude them once the locking is proved for every finite right half, which is the open lead in
[the period-four finding](../../findings/columns/period-four-locking.md).

**Related attempts that stall the same way.**

- Counting windows near the center: a left half under the constraint needs at most about $\sqrt{2}^{\,a}$ windows of
  radius $a$, below the right half's $1.55^a$, so counting windows gives no contradiction.
- An entropy count: under an eventual period the regular left side at time $t$ would be a function of the center and
  column 1 on $[t, 2t]$, but that region is the same word for every $t$ in a residue class modulo 8 (to depth 400), so
  no entropy count applies.
- Decoupling: under an eventual period the halves evolve independently, the left with boundary $c(t)$, $c(t+1)$ and the
  right with drive $c$, and meet only in the white-time condition $\text{col}_{-1} \oplus \text{col}_1 = c(t+1)$. Both
  outputs come from finite data, so no entropy count separates them.
