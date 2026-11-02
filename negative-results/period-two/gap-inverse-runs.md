---
title: Over the gap shift the inverse diagonal has constant runs as long as a fair coin predicts, 15 at s = 149, so no run bound below 15 holds there and the counts show no sign of a larger one
category: period-two
problems: [1]
status: negative
kind: refuted
evidence: [computations/gap_inverse_runs.py, computations/gap_inverse_runs.c]
---

# Over the gap shift the inverse diagonal has constant runs as long as a fair coin predicts, 15 at s = 149, so no run bound below 15 holds there and the counts show no sign of a larger one

**Question.** Beside an alternating center, at a white step the kit's endpoint symbol
$e_j = \mathrm{encodePair}(x_{-1}, x_{-2})$ at time $o + 2j + 2$ (kit main, `Rule30SEPToPeriodTwo.actualEndpoint`) is 1
or 2, and since the center turns black at the next step, $x_1 = \lnot x_{-1}$: column 1 is black exactly when $e_j = 1$
(`pair_one_requires_right`). In the kit's gate trap (`Rule30GateTrap.gaps_of_entry`) each black cell of column 1 at the
white steps is followed by the next one 3 or 5 white steps later. So a right half in the trap gives a stream $e$ that is
eventually 2 forever, whose inverse is then eventually the alternating stripe (`inverse_eventual_twos`), or eventually in
the gap shift
$$X_{\mathrm{gap}} = \{1\,2\,2,\ 1\,2\,2\,2\,2\}^{\omega},$$
of growth rate $\lambda = 1.19386$ ($\lambda^5 = \lambda^2 + 1$, 0.2556 bits per symbol). The statement about streams
that this class needs, the stream counterpart of the kit's open `Q01Gap` (the link between the two is not proved; see
the end), is

> **GapCTS.** No stream that is eventually in $X_{\mathrm{gap}}$ has $I = \mathrm{inverse}\ e$ eventually constant
> $c \in \{2, 3\}$.

The streams of $X_{\mathrm{gap}}$ are hard-core, so GapCTS is the case of the kit's open `ConstantTailSeparator` (kit
main, `Rule30SeparatorBridge`) for the streams that are eventually in the gap shift, and follows from it.

$I(s)$ reads $e$ only on $[\lfloor s/2 \rfloor, s]$, and every word of the gap shift extends to the left by every length,
so GapCTS is the same statement for the streams of $X_{\mathrm{gap}}$ in every phase. A route to it: a run bound
**RB(R)**, that for every stream of $X_{\mathrm{gap}}$ in every phase, $I$ has no run of a constant $c \in \{2, 3\}$ longer
than $R$. RB(R) implies GapCTS at once, and a closed set of windows of the cone on which no run longer than $R$ starts
would prove RB(R) in the kernel, as the trap modules here do. Over the gap words of length 60 the longest run is 8, from
$s = 17$ to $s = 24$, and none is longer, so a search to $s = 60$ alone would suggest a bound. (The kit's `Rule30SurvivalBridge.RunBound` is a
different statement, about runs of a frontier with no repeated scalar.)

**The coding.** `chart_check` builds the diagram of a right half driven by the kit's `altCol` and solves the left half
sideways from the center; there $o = 1$, every $e_j$ is binary, $e_j = 1$ exactly when the kit's `u R (j + 1)` is black,
and the kit's `actual_cone_chart` holds on all 2,016 entries checked for each of six right halves. `trap_streams` runs
the empty right half and 199 random halves below $2^{20}$ for 6,000 steps: 195 of the 200 enter the gap trap of
[the gate census](../../findings/period-two/gate-census.md) by white step 628, the empty half at step 146 as in the
kit's `u_empty_146`, and in all 195 column 1 after the entry, read as $e$, is a word of $X_{\mathrm{gap}}$ (at least
2,371 symbols each).

**What was done.** For a window $v = e_h e_{h+1} \dots$ the rows $E_i[0] = 3 - v_i$, $E_i[1] = \varphi(v_{i-1}, E_i[0])$,
$E_i[t] = \varphi(E_{i-1}[t-2], E_i[t-1])$ for $t \le 2i$ do not depend on $h$, and $I(h + i) = E_i[h + i]$ for every
$h \le i$. A run of length $r$ at $s$ is then a property of the window $e_{\lfloor s/2 \rfloor} \dots e_{s+r-1}$. Let
$N(s, r)$ be the number of words of the gap shift of length $\lceil s/2 \rceil + r$ that, as that window, carry a run of
length at least $r$ at $s$ (not necessarily maximal), and $R(s)$ the longest run at $s$. Since $\varphi(a, \cdot)$ is a
bijection, at most one symbol continues a run, so a search over all 24,179,501 gap words of length 90 and all shorter
ones, with each run followed to its end, gives $N(s, r)$ exactly for every $s \le 180$. The fair-coin model makes every
forced symbol uniform on the four symbols, so its expected count is $2 \cdot 4^{-r} |L_{\lceil s/2 \rceil + r}|$, with
$L_n$ the gap words of length $n$; it grows like $\lambda^{s/2}$, and its records grow like
$(s/2) \ln \lambda / \ln(4/\lambda) = 0.0733\,s$ (a heuristic). The search agrees with a brute force by the kit's
recursion on every gap word of length 25, and its C and Python versions agree.

**Outcome.** The counts follow the coin. Over $90 \le s \le 180$, $\sum_s N(s, r)$ is 1.000 to 1.003 times the coin's
for $r \le 7$, 0.87 to 1.27 times for $8 \le r \le 14$ and 0.63 at $r = 15$ (5 runs against 7.9), and $N(s, r)$ grows per two steps of $s$ by 1.1939, 1.1934, 1.1968 and 1.2018 for
$r = 1, 3, 5, 7$, against $\lambda = 1.1939$. The long runs:

| $r$ | first $s$ with a run $\ge r$ | the coin's (expected count reaches 1) | $\sum_{90 \le s \le 180} N(s,r)$ over the coin's | runs $\ge r$ at $s \le 180$, against the coin's |
|---:|---:|---:|---:|---:|
| 8 | 17 | 62 | 0.973 | 36,488 / 37,500 |
| 9 | 99 | 75 | 0.966 | 10,816 / 11,200 |
| 10 | 109 | 89 | 1.051 | 3,509 / 3,340 |
| 11 | 126 | 103 | 1.267 | 1,263 / 997 |
| 12 | 149 | 116 | 1.267 | 377 / 298 |
| 13 | 149 | 130 | 0.946 | 84 / 88.8 |
| 14 | 149 | 143 | 0.868 | 23 / 26.5 |
| 15 | 149 | 157 | 0.632 | 5 / 7.91 |
| 16 | none | 171 | 0 | 0 / 2.36 |

The longest run at $s \le 60$ is 8, at $s \le 120$ it is 10 and at $s \le 180$ it is 15: $I(149) = \dots = I(163) = 3$
for the gap word whose window from cell 74 is
$122221222212212222122122122122122122122122221221221221221222212222122122122221221221221222$ (checked on a whole word
of 164 symbols by the kit's recursion in the tests). So **RB(R) is false for every $R \le 14$**. Below $s \approx 90$ the
long runs are rarer than the coin's ($N(s, 5)$ and $N(s, 7)$ grow by 1.131 and 1.102 per two steps on
$20 \le s \le 90$, and no run of 7 or more starts at $19 \le s \le 71$); this transient is what kept the record at 8
to $s = 60$. Over 100,000 random gap streams of length 400 from the measure of maximal entropy, the frequency of a run of length at
least $r$ at $s$, by blocks of 40 positions from $s = 80$ to 359, is $3.11$ to $3.19 \times 10^{-2}$ for $r = 3$,
$1.92$ to $2.00 \times 10^{-3}$ for $r = 5$ and $0.95$ to $1.35 \times 10^{-4}$ for $r = 7$, against the coin's
$2 \cdot 4^{-r} = 3.13 \times 10^{-2}$, $1.95 \times 10^{-3}$ and $1.22 \times 10^{-4}$; the longest run of a stream
is at most 13.

**Controls.** The binary and hard-core classes, the classes of the kit's `BWH` and `ConstantTailSeparator`, give the same
picture. Binary words to length 26 ($s \le 52$): $\sum N / \text{coin}$ is 0.995 to 1.006 for $r \le 9$, $N(s, r)$
grows by 2.005, 2.015 and 2.021 per two steps for $r = 3, 5, 7$ against 2, and the record is 23 at $s = 48$ (coin slope
0.5). Hard-core words to length 36 ($s \le 72$): 0.995 to 1.012 for $r \le 10$, growth 1.618, 1.615 and 1.604 against
1.618, record 17 at $s = 72$ (coin slope 0.266). In the sampling of 100,000 streams of length 400 the frequencies at
$80 \le s < 360$ are within 4% of the coin's for $r = 3$ and 5 and within 25% for $r = 7$ in all three classes. Near
the top of each table the counts fall below the coin's: for binary words from $r = 22$ (36 runs against 128), where
the kit's open `BWH` would bound a run at $s = 2n$ by $n + 1$ (no witness for $7 \le n \le 31$), at the coin's slope;
for hard-core words from $r = 13$ (2,490 against 3,180). For the gap shift the top counts, 84, 23 and 5 against 88.8,
26.5 and 7.91, are small.

**What it means.** The route stops at its first step. RB(R) is false for $R \le 14$, so no closed set of windows
certifies it there, and the counts at $r \le 7$ grow with $s$ at the coin's rate $\lambda^{s/2}$ while those up to
$r = 15$ stay near the coin's totals, so the records are expected to keep growing about linearly, with slope near 0.07 (a heuristic): a bound for every $R$ is false in
spirit, and the search for a closed set of cone windows that bounds the runs was not started. The gap shape does not
shorten the runs: the inverse diagonal of a gap stream behaves, run by run, like that of a binary or hard-core stream.

What survives is GapCTS itself. In the coin model each window carrying a run has on average about
$\lambda / 4 = 0.30$ extensions that continue it (a random stream continues it with probability 1/4), so for each $s$ the expected number of runs at $s$ longer than $r$ tends to 0 as $r$ grows: the model has no infinite
run, and the counts stay near it at every $r$ measured. GapCTS stays open as the statement that every forced run over
the gap shift dies, with no uniform bound on when, the same shape as the kit's `BWH`
([the forced runs](../../findings/period-two/wedge-forced-runs.md), [the survivor
mechanism](wedge-survivor-mechanism.md)). The class of streams that are eventually in $X_{\mathrm{gap}}$ is closed under
shifts and under putting symbols in front, which is what the kit's `separator_excludes_finite_peel_rank` uses of the
hard-core class, so the same steps should give that GapCTS also excludes a finite peel rank in this class (not checked
in Lean). The link from GapCTS to `Q01Gap` is what a chart from finite left halves to streams of finite peel rank would
give when restricted to free bits whose complement is spaced 3 or 5 apart; that chart is not proved here.

## Reproduce

```bash
python -m computations.gap_inverse_runs check      # the coding and the gap streams of 200 right halves: a few seconds
python -m computations.gap_inverse_runs exhaust    # the gap shift to s = 180: about 70 s on two threads
python -m computations.gap_inverse_runs controls   # binary to s = 52, hard-core to s = 72: about 85 s
python -m computations.gap_inverse_runs sample     # 100,000 streams of length 400 in each class: about 25 s
```
