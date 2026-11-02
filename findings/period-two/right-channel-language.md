---
title: The exact right channel beside an alternating center has entropy falling from 0.36 to 0.12 bit per white step between 8 and 28 columns, and every right half of up to 14 cells is read by it from the white step 20 on
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/right_channel_language.py]
---

# The exact right channel beside an alternating center has entropy falling from 0.36 to 0.12 bit per white step between 8 and 28 columns, and every right half of up to 14 cells is read by it from the white step 20 on

Drive a right half with an alternating center and read its window of columns $1, \dots, W$ at the white steps of the
center, with column $W + 1$ free at both steps of each double step. Let $S_0$ be every window and $S_{i+1}$ the
double steps, with every input, of the windows of $S_i$. The chain decreases and stops at its fixpoint $E_W$, the
limit set, after a finite number of images, the *chain length*. Every right half, finite or not, has its window in
$E_W$ from the white step equal to the chain length on, so column 1 at the white steps, the kit's $u_R$, is from then
on column 1 along a path of double steps in $E_W$: the *right channel* at width $W$. Its language is a sofic shift;
this entry computes it exactly at every even width from 8 to 28.

1. **The ladder.** The chain length, the size of $E_W$, the number of states of the subset automaton of the
   language, and its entropy per white step are in the table below. The entropy falls from 0.356 at 8 columns to
   0.244 at 14 and 0.122 at 28, against 1 for the kit's `Q01`, which asks a finite left half to absorb any sequence.
2. **The reduction, in Lean.** Because entry into $E_W$ holds for every right half, the kit's `CQ01`, and with it
   period two for the single cell, follows from $\mathrm{Q01Right}(W)$, the statement that no finitely supported
   constrained start has the complement of its free bits equal, from some step on, to column 1 along a path in $E_W$,
   at any one width $W \ge 1$ ([ChannelLanguage](../../Rule30Open/PeriodTwo/ChannelLanguage.md)). At 14 columns the
   module also checks $E_{14}$ in the kernel: 2,436 windows, entered by every right half by the white step 20.
3. **The check of the reduction.** Every right half of up to 14 cells, in both phases, and the 200 halves of
   `gap_inverse_runs check` (cells up to 20), run directly for 1,000 steps: at every white step from 20 to 499 the
   window lies in $E_{14}$, and column 1 from the white step 20 on is read by the subset automaton of 14 columns.
   33,168 runs, no failure.
4. **Where the route stops.** At no width computed does the channel show that every gate eventually lies in the gap
   trap or is eventually periodic. Below 16 columns the window cannot see the gap trap. From 16 columns on, the window
   graph on $E_W$ keeps strongly connected components that hold cycles and are neither terminal, nor inside the gap
   trap, nor locked to a period (91,029 and 21,138 windows at 28 columns), so a path can stay in them forever;
   and the subset automaton keeps components that a play can leave (*wandering* components) with growth above 1. The largest wandering growth falls with the width,
   1.158 at 16 columns, 1.111 at 20, 1.0964 at 24, 1.0926 at 26 and 1.0786 at 28, where for the first time it is below
   the growth of the terminal component (1.0884); whether it reaches 1 at some width is open. No language-level entry
   statement is claimed here.

## The ladder

The growths are those of the strongly connected components of the subset automaton that hold a cycle and have
growth above 1 (its spectral radius per white step), T marking a terminal component, one no letter leaves. The
entropy is $\log_2$ of the largest.

| $W$ | chain length | $\lvert E_W \rvert$ | subset states | entropy per white step | growths of the positive components |
|---:|---:|---:|---:|---:|---|
| 8 | 3 | 112 | 43 | 0.3562 | 1.2801 T |
| 10 | 6 | 345 | 111 | 0.3161 | 1.2450 T |
| 12 | 13 | 986 | 322 | 0.2578 | 1.1957 T, 1.1057 |
| 14 | 20 | 2,436 | 562 | 0.2442 | 1.1844 T |
| 16 | 27 | 6,432 | 1,344 | 0.2116 | 1.1580, 1.0962 T |
| 18 | 76 | 13,891 | 2,496 | 0.1846 | 1.1365, 1.0921 T |
| 20 | 45 | 35,495 | 4,427 | 0.1519 | 1.1110, 1.0921 T |
| 22 | 59 | 83,309 | 7,782 | 0.1372 | 1.0998, 1.0921 T, 1.0831 |
| 24 | 82 | 199,007 | 19,239 | 0.1327 | 1.0964, 1.0920 T, 1.0578 |
| 26 | 84 | 497,528 | 52,762 | 0.1277 | 1.0926, 1.0909 T, 1.0467, 1.0298 |
| 28 | 128 | 1,172,176 | 127,589 | 0.1222 | 1.0884 T, 1.0786, 1.0414 |

The chain length is not monotone in $W$ (76 at 18, 45 at 20). The subsets of the automaton are held as sorted index
arrays into $E_W$ only while they wait to be expanded, and the table of states keeps a 16-byte digest of each; the run
at 26 columns stays under 1 GB, the run at 28 under 1.5 GB. From 16 to 26 columns the largest growth, and so the
entropy, is that of a wandering component; at 28 columns it is that of the terminal component.

## The window graph

The double-step graph on $E_W$ has few strongly connected components with a cycle (`window_components`):

| $W$ | components with a cycle (windows, gcd of the cycle lengths; T terminal; L column 1 a function of the class; G inside the gap trap; E holds the aligned ether) |
|---:|---|
| 12 | 792 (1, T, E); 49 (1) |
| 14 | 2,005 (1, T, E); 9 (8, L) |
| 16 | 2,555 (1, E); 760 (1, T, G); 35 (16, L); 10 (8, L) |
| 18 | 5,651 (1, E); 2,110 (1, T, G); 10 (8, L) |
| 20 | 11,606 (1, E); 5,352 (1, T, G); 91 (4, T, L); 13 (5, L, G); 10 (8, L) |
| 22 | 13,706 (1, T, G); 8,963 (1); 6,334 (1, E); 265 (4, T, L); 6 (5, L, G); 4 (4, L) |
| 24 | 36,191 (1, T, G); 16,385 (1); 11,848 (1, E); 798 (4, T, L); 532 (3, L); 14 (5, L, G) |
| 26 | 92,196 (1, T, G); 38,337 (1); 21,859 (1); 2,203 (4, T, L); 1,131 (3, L); 229 (1); 92 (2, L, E); 53 (4, T, L); 39 (5, L, G); 5 (3, L); 4 (3, L) |
| 28 | 235,926 (1, T, G); 91,029 (1); 21,138 (1); 6,025 (4, T, L); 2,349 (3, L); 1,255 (2, L); 175 (19, L); 160 (4, T, L); 109 (2, L, E); 105 (5, L, G); 9 (7, L); five of 3 to 5 windows (L) |

"Inside the gap trap" means that every window of the component that is black in column 1 is, cut to 16 columns, an
entry window of the gap trap (`gate_census.gap_entry`): every play from it, whatever the cells beyond, has the black
cells of column 1 come 3 or 5 white steps apart, so a path in the component does from its first black window on. At every width from 16 to 28 columns, every terminal component is inside the gap trap or has column 1
locked to a period, which the kit's absorption route excludes outright. A path that ends in a terminal component
therefore gives either the setting of the kit's `Q01Gap` or a periodic column. The wandering components are the
obstacle: they hold cycles, so a path can stay in them forever. The two windows of the aligned ether
(`three_set_game.ether_cycle`), which every deep member of the kit's ether family shows at every white step ([the
residue](../../negative-results/period-two/game-residue.md)), lie in $E_W$ at every width, since the ether is a genuine
orbit: in the terminal component at 12 and 14 columns, in a wandering component with column 1 not locked from 16 to 24
columns, and at 26 and 28 columns in a wandering component of 92 and 109 windows on which column 1 alternates. There
the wandering components that are not locked (38,337, 21,859 and 229 windows at 26 columns, 91,029 and 21,138 at 28)
do not hold it.

## Comparison with `Q01Gap`

The kit reduces `CQ01` for the right halves that enter its gate trap to `Q01Gap`, a statement that no finite left half
absorbs a sequence of the gap shift, with blocks $001$ and $00001$, of entropy 0.256 per white step; entry into the
trap is a separate open statement, checked to 20 cells ([the census](gate-census.md)). At 14 columns, the languages of
$\mathrm{Q01Right}(14)$ and `Q01Gap` are not nested, so neither hypothesis follows from the other by inclusion of languages: the gap shift has
larger entropy than the channel at 14 columns (0.256, from [the gap
shift](../../negative-results/period-two/gap-inverse-runs.md), against 0.244) and so is not inside it, and the channel holds sequences outside the gap shift, such as the
alternation of the aligned ether. What $\mathrm{Q01Right}$ gains is that it needs no entry: entry into $E_W$ holds for
every right half by finiteness of the windows, in Lean. What it costs is the language: from 16 to 26 columns its
entropy is that of a wandering component, above that of the terminal component of the subset automaton (growth 1.092
from 18 to 24 columns); at 28 columns the terminal component carries it (growth 1.0884, entropy 0.122), with a
wandering component of growth 1.0786 beside it.

## Reproduce

```bash
python -m computations.right_channel_language ladder --widths 8 10 12 14 16 18 20 22 24   # about 70 s
python -m computations.right_channel_language ladder --widths 26   # 3 to 6 min, under 1 GB
python -m computations.right_channel_language ladder --widths 28   # about 30 min, 1.4 GB
python -m computations.right_channel_language kill --width 14 --cells 14 --steps 1000 --start 20   # about 35 s
python -m computations.right_channel_language lean --width 14   # the bitmaps of the Lean module
```

`tests/test_right_channel_language.py` checks the chain and the limit set at 8 cells against an iteration on Python
sets with `gate_census.double_step`, and that the limit set is its own image; the numbers of words of length 10, 11
and 12 that the subset automaton reads at 8 cells (59, 79 and 104) against an enumeration of the paths with their
words; that column 1 of every right half of up to 8 cells in both phases, from a direct run of
`right_half.column_one`, is read by the automaton of 10 cells from the white step 20 on, and that the vectorized run
of the kill test gives the same column; and that the bitmaps of the Lean module are those of the image chain at 14
cells.
