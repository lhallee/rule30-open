---
title: BWH, and WeakBWH with any horizon on infinitely many depths, imply the binary separator BinaryCTS, which holds exactly when some horizon works at every depth
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.WedgeLadder
headline: [bwh_binaryCTS, weakBWH_binaryCTS, bwh_constantTailSeparator, binaryCTS_iff_horizon, wedge_vacuum, binaryCTS_excludes_finite_peel_rank, weakBWH_small]
kit: new
kit_modules: [Rule30WedgeBridge, Rule30SeparatorBridge, Rule30SeparatorEquivalences]
evidence: [computations/wedge_ladder.py, computations/wedge_hypotheses.py]
---

# BWH, and WeakBWH with any horizon on infinitely many depths, imply the binary separator BinaryCTS, which holds exactly when some horizon works at every depth

The kit's main branch states open hypotheses on streams $e : \mathbb N \to \{0, 1, 2, 3\}$ (`Rule30WedgeBridge`,
`Rule30SeparatorBridge`, from pull request #76, [kit pull requests](../../literature/kit-pull-requests.md));
[WedgeSmall](WedgeSmall.md) restates the definitions as `Rule30Open.WedgeKit`: the table $\varphi$, the inverse
$I_e(t) = C(t, 0)$ of the cone, the peel $(Px)(t) = \varphi(x_t, x_{t+1})$ and the wedge $W_n e = P^n I_e$. A symbol is
binary when it is 1 or 2, and a stream is hard-core when it is binary with no 1 after a 1. `BWH` says that for
$n \ge 7$ and $c \in \{2, 3\}$ no binary word $e_0 \dots e_{2n+1}$ has $W_n e(t) = c$ for $t < n + 2$. The kit's
`ConstantTailSeparator` (`SEP`, equivalent to its orbit separator) says that no hard-core stream has $I_e$ eventually
constant $c$. The kit proves `BWH` and `SmallRW` imply `RW`, `RW` implies `SEP`, and `SEP` excludes period two.

This module restates `shift`, `cone_shift`, `rotated_peel`, `peelPow_translate`, `peelPow_inside`, `wedge_shift` (kit
`Rule30WedgeBridge`), `shiftN`, `rotated_iterate`, `HardCore`, `EventuallyConstant`, `ConstantTailSeparator`,
`prependTwos`, `unphi`, `lift`, `liftWord` (kit `Rule30SeparatorBridge`) and `peel_zero_classification` with its
lemmas (kit `Rule30SeparatorEquivalences`) verbatim from the kit's main branch, with the kit's proofs, in the namespace
`Rule30Open.WedgeLadder`. Two statements are new:

- `BinaryCTS`: no binary stream has $I_e$ eventually constant $c \in \{2, 3\}$. It is `SEP` with the hard-core
  condition dropped, so it is the stronger statement.
- `WeakBWH S L`: for every $n \in S$ and $c \in \{2, 3\}$, no binary word of length $n + L(n)$ has $W_n e(t) = c$ for
  $t < L(n)$. `BWH` is `WeakBWH` with $S = \{n \ge 7\}$ and $L(n) = n + 2$ (`bwh_iff_weakBWH`). A larger horizon makes
  it weaker.

## Results

- **`weakBWH_binaryCTS`**: if $S$ is infinite, `WeakBWH S L` implies `BinaryCTS`, for every horizon $L$.
  **`bwh_binaryCTS`**: `BWH` implies `BinaryCTS`.
- **`bwh_constantTailSeparator`**: `BWH` alone gives the kit's `ConstantTailSeparator`, with no `SmallRW` and no `RW`
  (`binaryCTS_constantTailSeparator`: a hard-core stream is binary).
- **`binaryCTS_iff_horizon`** (compactness): `BinaryCTS` holds exactly when one horizon function works at every depth,
  $\exists L$, `WeakBWH (fun _ => True) L`. `binaryCTS_horizon` gives the horizon at each depth and value.
- **`binaryCTS_excludes_finite_peel_rank`**, **`binaryCTS_orbit`**: under `BinaryCTS` no peel $P^d I_e$ of a binary
  stream is eventually 0, and $I_e$ is never `liftWord u (const c)`: the kit's consequences of `SEP`, for binary streams.
- **`wedge_vacuum`**: $\varphi(0, 0) = \varphi(2, 2) = \varphi(3, 3) = 0$, so $W_n e(t) = c$ for $t < L$ gives
  $P^{n+k} I_e(t) = 0$ whenever $k \ge 1$ and $t + k < L$; for `BWH`'s horizon, $t + k \le n + 1$ (`wedge_vacuum_bwh`).
- **`weakBWH_small`**: `WeakBWH` holds for $2 \le n \le 6$ with the horizon $L(n) = 2n$.

With [WedgeLadderQ01](WedgeLadderQ01.md), `BinaryCTS` is the kit's `Q01`, so `BWH`, and `WeakBWH` on infinitely many
depths with any horizon, exclude an eventual period two of the official center column.

## The ladder

Each rung says that every forced run of a constant wedge dies, over a class of streams, within a horizon. Past a free
prefix of $n$ symbols each symbol of a run is forced ([forced runs](../../findings/period-two/wedge-forced-runs.md)),
so each rung is a statement about $2^n$ forced runs at depth $n$.

| Statement | Streams | Horizon | Depths | Where | Status |
|---|---|---|---|---|---|
| `BWH` | binary | $n + 2$ | $n \ge 7$ | kit main | open; no witness for $7 \le n \le 31$ by search; its bound fails at $n = 5$ and $6$ |
| `RW` | binary, hard-core from $n$ on, ending $1, 2$ | $n + r + 2$, $r \le 2$ | $n \ge 1$ | kit main | open; `SmallRW` ($n < 7$) proved in [WedgeSmall](WedgeSmall.md), no witness for $n \le 26$ by search |
| `WeakBWH S L` | binary | $L(n)$ | an infinite set $S$ | here | open for every $L$; $L(n) = 2n$ holds for $2 \le n \le 6$ |
| $\exists L$, `WeakBWH` (all $n$) $L$ | binary | some $L(n)$ | every $n$ | here | equivalent to `BinaryCTS` |
| `BinaryCTS` | binary | infinite | | here | equivalent to the kit's `Q01` ([WedgeLadderQ01](WedgeLadderQ01.md)) |
| `ConstantTailSeparator` = `SEP` | hard-core | infinite | | kit main | open |
| stream form of `Q01Gap` | binary, 1s eventually 3 or 5 apart | infinite | | kit main (`Rule30GateTrap`) | open; not formalized here |

The arrows that are proved:

- `BWH` $\Rightarrow$ `WeakBWH` on $\{n \ge 7\}$ with $L(n) = n + 2$ $\Rightarrow$ `BinaryCTS` (here), and `WeakBWH S L`
  $\Rightarrow$ `BinaryCTS` for every infinite $S$ and every $L$ (here).
- `BinaryCTS` $\Leftrightarrow$ $\exists L$, `WeakBWH` (all $n$) $L$ (here) $\Leftrightarrow$ `Q01` ([WedgeLadderQ01](WedgeLadderQ01.md)).
- `BinaryCTS` $\Rightarrow$ `SEP` (here); `BWH` $\Rightarrow$ `RW` $\Rightarrow$ `SEP` (kit, with `SmallRW` from
  WedgeSmall); mortality of the kit's frontier $\Rightarrow$ `Q01` (kit `Q01_of_mortality`); `Q01` $\Rightarrow$
  `Q01Gap` (kit `Q01Gap_of_Q01`); `Q01` and `SEP` each exclude an eventual period two (kit).

Open: `SEP` $\Rightarrow$ `BinaryCTS` (the hard-core property of the kit's chart comes from the row's right half, which
`Q01` does not have); `RW` $\Rightarrow$ `BinaryCTS`; `Q01` $\Rightarrow$ `BWH`, which asks the horizon $n + 2$ where
`Q01` gives only some horizon; `Q01` $\Rightarrow$ mortality (the kit states it open). The `Q01Gap` row restricts
`BinaryCTS` to streams whose symbols 1 come 3 or 5 apart from some index on: a symbol 1 of the chart's endpoint is a
white cell of column $-1$ at an odd step ([WedgeLadderQ01](WedgeLadderQ01.md)), and `Q01Gap` asks about the white cells
of that column at the odd steps in the kit's mirrored frame (`Rule30ZeroBoundary`). That frame is on the kit's main
branch only and its match with the chart's steps is not checked, so the row is a description, not a theorem.

## The argument

**The rotation** (kit `rotated_iterate`). $W_n(e_{\cdot + n})(t) = I_e(t + 2n)$: peeling the inverse of a shifted
stream is the inverse two steps later (`rotated_peel`), and $n$ shifts give $2n$ steps.

**`WeakBWH` implies `BinaryCTS`.** Let $e$ be binary with $I_e(t) = c$ for $t \ge N$. Take $n \in S$ with $n \ge N$.
The stream $e_{\cdot + n}$ is binary at every index, and $W_n(e_{\cdot + n})(t) = I_e(t + 2n) = c$ for every $t$, so it
is a witness against `WeakBWH S L` at depth $n$ for every horizon. Only the binary property of $e$ is used. A hard-core
stream is binary, so `BinaryCTS` gives `SEP` at once. No `SmallRW` is needed because $n$ can be taken as large as one
likes.

**Compactness.** Suppose `BinaryCTS` and suppose that at some depth $n$ and value $c$ every horizon has a witness. Call
a word unbounded when every horizon has a witness that starts with it. The empty word is unbounded, and one of the two
binary children of an unbounded word is unbounded (`unbounded_child`): the witness for a horizon beyond both children's
bounds has a binary symbol after the word, so it starts with one of them. Following unbounded children gives an
infinite binary stream (`branch`) each of whose prefixes is unbounded; $W_n e(t)$ reads only $e_0, \dots, e_{t+n}$
(`wedge_local`), so $W_n e(t) = c$ for every $t$ (`infinite_run_of_unbounded`). Then $P^n I_e$ is constant, which
`BinaryCTS` excludes: prepending $n$ symbols 2, which keeps the stream binary, turns a constant $P^n I_e$ into an
eventually constant inverse by the rotation (`binaryCTS_peel`, the binary form of the kit's
`constant_separator_implies_full_orbit_separator`). So each depth and value has a horizon with no witness, and a larger
horizon has none either (`no_run_mono`); the sum of the two horizons serves both values.

**The binary forms of the kit's consequences.** The kit's `separator_excludes_zero_cut` and
`separator_excludes_finite_peel_rank` use the hard-core property of the stream only through `hc_shift` and
`hc_prepend`, and through the binary symbol at index 0. Shifts and prepended 2s keep a stream binary
(`binary_prepend`), and $\partial(1) = 2$, $\partial(2) = 1$ are not 0, so the kit's proofs go through for binary streams
(`binaryCTS_peel_zero`, `binaryCTS_excludes_zero_cut`, `binaryCTS_excludes_finite_peel_rank`). The kit uses
`normalizeSym` (the symbol 3 in a label word) only for the converse, from the orbit separator to the constant-tail
separator; `binaryCTS_orbit` takes every word over the four symbols.

**The vacuum.** If $W_n e(t) = c$ for $t < L$, then $P^{n+1} I_e(t) = \varphi(c, c) = 0$ for $t + 1 < L$, and the
peels of a run of zeros are zeros ($\varphi(0, 0) = 0$, `peelPow_zeros`, with `peelPow_locality`). In the chart of [WedgeLadderQ01](WedgeLadderQ01.md) the
zeros are the white cells left of a start's leftmost black cell.

**Horizon $2n$ for $2 \le n \le 6$.** WedgeSmall's depth-first search (`wsearch`, `wsearch_sound`, `wedgeL_spec`) with
the test `horizonTest n (2n) c` excludes every binary word of length $3n$ with a constant wedge $c$ of length $2n$; the
kernel evaluates the ten searches (`horizon_n2`, ..., `horizon_n6`, by `decide +kernel`). At $n = 1$ the horizon $2$
fails for $c = 3$. Beyond, the largest constant wedge $M(n, c)$ of the [forced runs](../../findings/period-two/wedge-forced-runs.md)
is at most 28 for $7 \le n \le 31$, below $2n$, by computation.

## BWH is the kit's Q01 at a linear horizon (computed)

The chart of [WedgeLadderQ01](WedgeLadderQ01.md) sends a start of the zero-driven left half whose leftmost black cell is
at $-m$, $m = 2n + 2$, to a binary stream with $W_n e(t) = 2$ wherever the chart reaches, and a start with black cells
at $-m$ and $-(m - 1)$, $m = 2n + 3$, to one with $W_n e(t) = 3$. The symbol $e_j$ is binary exactly when column $-1$
is black at step $2j + 2$. By the kit's `barrier_exists`, the starts with leftmost black cell at $-(2n + 2)$ whose
column $-1$ is black at the even steps up to $2n$ are $2^n$, one for each value of the column at the odd steps
$1, \dots, 2n - 1$, which are the free symbols $e_0, \dots, e_{n-1}$; past them each symbol is forced. So, on paper,
`BWH`$(n, 2)$ says that no start with leftmost black cell at $-m$, $m = 2n + 2$, keeps column $-1$ black at every even
step up to $2m$, and `BWH`$(n, 3)$ says the same for the starts with black cells at $-m$ and $-(m - 1)$, $m = 2n + 3$,
up to step $2m - 2$. This finite form is not in Lean.

`wedge_ladder.py` checks the identification by simulation: for $1 \le n \le 12$ and both values of $c$ it builds every
such start from its column, runs it forward, and finds that each endpoint equals the forced run of `wedge_hypotheses.py`
with the same free prefix, symbol for symbol, and that the first even step at which column $-1$ turns white is
$2K + 2$, $K$ the number of binary symbols of the run. The latest such step, against the horizon of `BWH`:

| $n$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $c = 2$: latest step / $2m$ | 6 / 8 | 10 / 12 | 10 / 16 | 14 / 20 | 16 / 24 | **32** / 28 | 30 / 32 | 30 / 36 | 30 / 40 | 40 / 44 | 42 / 48 | 44 / 52 |
| $c = 3$: latest step / $2m - 2$ | 8 / 8 | 8 / 12 | 16 / 16 | 16 / 20 | **28** / 24 | 26 / 28 | 28 / 32 | 32 / 36 | 36 / 40 | 40 / 44 | 40 / 48 | 48 / 52 |

The two bold entries are the two depths below 7 at which the bound of `BWH` fails ($M(5, 3) = 8$ and $M(6, 2) = 9$). So `BWH` is the kit's `Q01` for starts of width $m$ with the
time horizon $2m$, the kind of bound that [the left half alone](../../findings/period-two/left-half-alone.md) measures
for the integer form of the same left half.

```bash
python -m computations.wedge_ladder --n 1 12    # the table: a few seconds
```

## What the kit has

The kit's main branch at [93d98bb](https://github.com/WolframInstitute/Rule30PrizeKit/commit/93d98bb) proves
`bwh_implies_rw` (which needs `SmallRW`), `rw_implies_constant_tail_separator`, `separator_equivalence`, and the
consequences of `SEP` for hard-core streams; it states no binary separator, no `WeakBWH`, and no implication from `BWH`
to `SEP` that avoids `RW`. The arrow `BWH` $\Rightarrow$ `SEP` through `rotated_iterate` alone, `BinaryCTS`, the
compactness equivalence and the horizon $2n$ are new. The pinned kit has none of these modules.
