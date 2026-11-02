---
title: Under a center column repeating 001, column 1 at the second white step has 1-runs of length at least 2 and 0-runs of length at least 3
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ThreeRuns
headline: [three_runs, three_runs_evolve, no_010_time, no_101_time, no_1001_time]
kit: new
kit_modules: [Rule30Ether, Rule30EtherThree, Rule30StripCertificates, Rule30EtherThreeSkeleton]
evidence: [computations/three_runs.py, computations/gap_traps.py]
---

# Under a center column repeating 001, column 1 at the second white step has 1-runs of length at least 2 and 0-runs of length at least 3

Let the center column repeat the block $001$ and let it drive the right half, from any initial right half, finite or
not. Each period of the block has two white steps; at the second of them, the one just before the black step, read
column 1. From the 14th reading on, these readings never contain $010$, $101$ or $1001$: every run of 1s has length at
least 2 and every run of 0s length at least 3. The proof is a rank certificate on a strip of 13 columns, checked by the
kernel: whatever the cells beyond column 13 do, the strip falls within 46 steps into a closed set of states on which no
reading completes one of the three words.

## Statement

The center is $c_{ph}(t) = 1$ exactly when $(t + ph) \bmod 3 = 2$ (the kit's `wordAt3 w001 (t + ph)`), and
$F = \mathrm{drv}(c_{ph}, R)$ is the kit's driven right half: column 0 is $c_{ph}$, column $p \ge 1$ starts as $R(p)$
and follows Rule 30. The second white steps are the $t$ with $(t + ph) \bmod 3 = 1$; the $i$-th of them is
$t_i = 3i + ((4 - ph \bmod 3) \bmod 3)$, and the $i$-th reading is $b_i = F(t_i, 1)$ (`reading R ph i`).
`NoShortRuns b i0` says that for every $i \ge i_0$ none of $b_i b_{i+1} b_{i+2} = 010$, $b_i b_{i+1} b_{i+2} = 101$,
$b_i b_{i+1} b_{i+2} b_{i+3} = 1001$ holds.

1. `three_runs`. For every $R : \mathbb{N} \to \mathrm{Bool}$ and every $ph$, `NoShortRuns (reading R ph) 14`.
2. `three_runs_evolve`. For every row `init` and time $T$ with `evolve init t 0 = wordAt3 w001 (t - T)` for all
   $t \ge T$, the readings $j \mapsto$ `evolve init (T + 3 j + 1) 1` satisfy `NoShortRuns _ 14`.
3. `no_010_time`, `no_101_time`, `no_1001_time`. The same by times: if $(u + ph) \bmod 3 = 1$, then
   $F(u,1)F(u+3,1)F(u+6,1)$ is neither $010$ nor $101$ when $u \ge 40$, and $F(u,1)F(u+3,1)F(u+6,1)F(u+9,1)$ is not
   $1001$ when $u \ge 37$. In each case the last reading is at time 46 or later.
4. `ThreeRuns.rank_bound`. Along every driven right half, the certificate's rank of the state at time $t$ is at most
   $46 - t$.

## Argument

1. **A finite state.** Columns $1, \dots, 13$ at time $t + 1$ are a function of columns $1, \dots, 13$ at time $t$,
   the center at time $t$ (known from the phase) and column 14 at time $t$, which is unknown. A state is a phase
   $p \in \{0, 1, 2\}$, a window $w < 2^{13}$ (bit $i$ is column $i + 1$) and the last three readings $s < 8$ (newest
   in bit 0). A step goes to phase $p + 1 \bmod 3$, to the window `stripStep 13 (p = 2) z w` for column 14 equal to
   $z$, and at phase 1 it appends the reading $w \bmod 2$, column 1 before the step, to $s$.
2. **The closed good set and its ranks.** Call a state good when, for every sequence of values of column 14, no
   reading from it on completes $010$, $101$ or $1001$. The good states form the greatest set $G$ that is closed under
   both successors and on which no step at phase 1 completes a word. Rank $G$ as 0, and give rank $k$ to a state
   outside the lower ranks whose two successors both have rank below $k$. Every one of the $3 \cdot 8 \cdot 2^{13}$
   states gets a rank, and the largest is 46.
3. **The kernel check** (`nodeOK`, `ok_p_s`, `parts_ok`). For every state: its rank is at most 46; at rank 0 both
   successors have rank 0 and, at phase 1, the reading does not complete a word (`badB`); at positive rank both
   successors have smaller rank. The ranks are packed 6 bits per window into 24 numbers, one per phase and readings,
   and each part is checked by `decide +kernel`. The check needs neither the construction of step 2 nor its claim of
   greatest set; any table that passes it proves the theorem.
4. **The driven half follows the states** (`win`, `win_enc`, `win_succ`, `suf`). The window of $F$ at time $t$ is
   encoded in the kit's form `EncF F 13 t 0`; the kit's `encF_step` moves it one step with column 14 as the unknown
   cell, and the center at time $t$ is black exactly at phase 2 (`ctr_eq`). The readings start as $s = 0$ at time 0.
5. **Rank falls to 0 by time 46** (`rank_bound`). At time 0 the rank is at most 46; a positive rank drops by at least
   1 per step and rank 0 stays 0, so the rank at time $t$ is at most $46 - t$.
6. **No word after time 46** (`no_bad`, `suf_three`). From time 46 on the state has rank 0, so a reading at phase 1
   completes no word against the stored readings. Three steps after a phase 1 step the stored readings have shifted
   by the reading of that step, so a word whose last reading is at time 46 or later, with all its readings at times
   0 or later, is checked against its true readings (`bad_010`, `bad_101`, `bad_1001`).
7. **Indices** (`three_runs`). The reading $b_{i+k}$ is at time $t_i + 3k$, and $t_i \ge 42$ for $i \ge 14$.
8. **Every row** (`evolve_eq_drv`, `three_runs_evolve`). From time $T$ on, the cells $p \ge 1$ of a row whose center
   repeats $001$ from $T$ are the right half driven by $c_0$ from the row at time $T$, by induction on the time as in
   the kit's `Rule30Ether.cell_eq_drv`. The second white steps are then the times $T + 3j + 1$.

## Relation to the kit

The kit's `Rule30EtherThreeSkeleton.skeleton_001` proves, for the single seed with center $001$ from $T$, that column
1 is eventually white at the first white step, and says that its strip certificates force nothing beyond that up to
width 13. Those certificates force fixed values of column 1 at given phases. The result here constrains the words
that column 1 reads at the second white step, where it is not eventually constant, so it is outside what those
certificates express; it holds for every right half, not only finite ones, and its form for rows is for every row
whose center repeats $001$. The kit's `Rule30EtherThreeLeft.col_m1_001` says that for the single seed column $-1$ at
these steps is the complement of column 1; with it, column $-1$ at these steps avoids $101$, $010$ and $0110$ from the
14th reading on. [ConstrainedLeft001](ConstrainedLeft001.md) uses the result in Lean to reduce $001$ to a left
statement with constrained free bits.

The certificate data are the greatest closed set and its layers of forced entry, computed by
[three_runs.py](../../computations/three_runs.py) as `greatest_trap` and `forced_layers` of
[gap_traps.py](../../computations/gap_traps.py) do, but with readings taken only at the second white step instead of
at every white step. The kernel check of step 3 does not depend on the script. [Reading
constraints](../../findings/columns/reading-constraints.md) puts this result among the word constraints that column 1
satisfies beside 23 blocks of period 3 to 7.

## Reproduce

```bash
python -m computations.three_runs --check   # the good set, entry within 46 steps, and the tables of the module
python -m computations.three_runs --lean    # the tables as Lean
```

`tests/test_three_runs.py` checks the window step cell by cell, the good set and the ranks at width 7 against a naive
greatest fixed point and naive backward layers, and a direct run of random halves from every phase.
