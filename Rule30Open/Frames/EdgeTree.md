---
title: Every edge code with bit 0 black is a rain code or passes through a branch state, where a column alternates and the next column equals it
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.EdgeTree
headline: [Frames.EdgeTree.rain_or_branch, Frames.EdgeTree.next_of_rain, Frames.EdgeTree.start]
kit: refines
kit_modules: [Rule30FrozenRuler, Rule30EdgeStaircases]
---

# Every edge code with bit 0 black is a rain code or passes through a branch state, where a column alternates and the next column equals it

For an edge code $c$, the row read from its right edge (the kit's `Rule30FrozenRuler.T`, the 2-adic map
$\Phi(y) = y \oplus (2y \lor 4y)$), write $\mathrm{col}\ c\ e\ i$ for bit $e$ of $\mathrm{iter}\ i\ c$, the column of
bit $e$ in time. A sequence *alternates* (`Alt`) when it flips at every step. A *rain pair* at $j$: column $j$
alternates and column $j + 1$ is its complement. A *branch state* at $j$: column $j$ alternates and column $j + 1$
equals it.

## Statement

- `start`: if $c(0) = 1$, then there is a rain pair or a branch state at 1.
- `next_of_rain`: a rain pair at $j + 1$ is followed by a rain pair or a branch state at $j + 2$.
- `rain_or_branch`: if $c(0) = 1$, then $c$ is `rainA` or `rainB`, or there is a branch state at some $j \ge 1$.
  No periodicity is assumed.

## Argument

1. Column 0 is black at every step (the kit's `iter_zero`), so column 1, whose input is column 0, flips at every step.
   Column 2's input, column 1 OR column 0, is black, so it alternates too.
2. Two alternating sequences are equal or complementary, depending on their first values (`alt_cases`). So columns 1
   and 2 form a rain pair or a branch state.
3. From a rain pair at $j + 1$, the input of column $j + 3$ is column $j + 2$ OR column $j + 1$, which is always black.
   So column $j + 3$ alternates, and by step 2 it is either column $j + 2$'s complement or equal to it.
4. If there is no branch state, every pair from $j = 1$ is a rain pair. At time 0 this gives $c(k + 2) = \lnot c(k + 1)$
   for every $k$, and with $c(0) = 1$ the code is `rainA` ($c(1) = 0$) or `rainB` ($c(1) = 1$).

## What it reduces and what is missing

This is the reduction skeleton of the second lemma of [the light-return words](../../findings/frames/light-return-words.md).
A periodic code that is not rain passes through a branch state. Both branch states are rotations in time of the one
state $(P, P)$, with $P = 0101\ldots$. The classification of the codes of period $L$ is therefore the statement that no
periodic walk of columns starts at that state. For $L \le 64$ that is the finite tree computed in that entry: 1,055
nodes of depth 14 at $L = 32$, and 85,887 nodes of depth 103 at $L = 64$.

Not in Lean here:
- the encoding of columns of an $L$-periodic code as $L$-bit words;
- a Boolean check that explores the tree from $(P, P)$;
- its soundness;
- the kernel-evaluated instances at 32 and 64.

Through `rain_or_branch`, those pieces would give the classification for every return time not divisible by 64 or 128.
