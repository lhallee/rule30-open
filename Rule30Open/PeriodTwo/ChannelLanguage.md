---
title: Period two follows from one statement about finite left halves, that none absorbs a word of the exact right channel, with no entry hypothesis on the right half
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.ChannelLanguage
headline: [cq01_of_q01Right, q01Right_of_q01, no_eventual_period_two_of_q01Right, not_finSupp_Psi_of_q01Right, channel14_limit, channel14_entry, q01Right14_iff]
kit: new
kit_modules: [Rule30PeriodTwoSideways, Rule30PeriodTwoCoupled, Rule30ZeroBoundary, Rule30Ether, Rule30EtherThreeReach]
evidence: [computations/right_channel_language.py]
---

# Period two follows from one statement about finite left halves, that none absorbs a word of the exact right channel, with no entry hypothesis on the right half

Drive a right half $R$ with the alternating center, black at the even steps (the kit's `altCol`), and read its
columns $1, \dots, W$ at the odd times, the white steps of the center. Column 1 there is the kit's $u_R$, and its
complement is the sequence of free bits of $\Psi_R$, the one left row that keeps the center alternating against $R$
(`Rule30PeriodTwoSideways.Psi_free`). The windows of $W$ columns that end paths of double steps of every length form
the *limit set* $E_W$; every right half, finite or not, has its window in $E_W$ from a fixed white step on. So
$u_R$ is eventually column 1 along a path in $E_W$, and the kit's `CQ01` follows from the statement that no finite
left half absorbs such a word:

$$\mathrm{Q01Right}(W) \implies \mathrm{CQ01} \implies \text{the center column of the single cell is not eventually of
period two}, \qquad \mathrm{Q01} \implies \mathrm{Q01Right}(W),$$

for every $W \ge 1$, with no hypothesis on where the right half goes. At $W = 14$ the limit set is explicit: 2,436
windows, entered by every right half by the white step 20.

## Statements

A window is a number $c < 2^W$, bit $i$ being column $i + 1$. The double step $\delta_W(c, x_1, x_2)$ is one step with
column 0 white and then one with column 0 black, $x_1$ and $x_2$ being column $W + 1$ at the two steps (`chanStep2`).
$c$ *reaches* at length $n$ when it ends a path $p_0, \dots, p_n = c$ with $p_{i+1} = \delta_W(p_i, x_1, x_2)$ for
some inputs (`Reach`), and $c \in E_W$ when it reaches at every length (`InLimit`).

- **Entry** (`chanWin_reach`, `exists_entry`). For each $W$ there is $N$ such that for every right half $R$ and every
  $s \ge N$ the window $w_R(s)$ of $R$ at the time $2s + 1$ (`chanWin`) lies in $E_W$.
- **The hypothesis** (`Q01Right`). $\mathrm{Q01Right}(W)$: no finitely supported $L$ with `InX L` has $s_0$ and
  windows $w_s \in E_W$ ($s \ge s_0$) with $w_{s+1}$ a double step of $w_s$ and bit 0 of $w_s$ equal to
  $\lnot\,$`zrow L (2 s + 1) 1`.
- **The reduction** (`not_finSupp_Psi_of_q01Right`, `cq01_of_q01Right`, `no_eventual_period_two_of_q01Right`). For
  $W \ge 1$, under $\mathrm{Q01Right}(W)$, $\Psi_R$ has infinitely many black cells for every right half $R$, so
  `CQ01` holds and `Rule30Prize.center` is not eventually of period two.
- **From Q01** (`q01Right_of_q01`). The kit's `Q01` excludes every finitely supported $L$ with `InX L`, so it gives
  $\mathrm{Q01Right}(W)$ at once.
- **The limit set at 14 columns** (`channel14_limit`, `channel14_entry`, `q01Right14_iff`). $c \in E_{14}$ exactly
  when `inE14 c`, a set of 2,436 windows given by bitmaps; $w_R(s) \in E_{14}$ for every $R$ and every $s \ge 20$;
  and $\mathrm{Q01Right}(14)$ is the hypothesis with `inE14` in place of $E_{14}$.

## The argument

**Windows.** `chanCode_drv_succ` says that one step of the driven row is one step of its code, from the kit's bit-mask
step `Rule30EtherThree.stepN` and its `testBit_stepN`; the code reads the first $W$ cells (`testBit_chanCode`), and
the column $W + 1$ enters as an input. From an odd time column 0 is white and then black, so
$w_R(s + 1) = \delta_W(w_R(s), x_1, x_2)$ with $x_1, x_2$ the cells of column $W + 1$ at the times $2s + 1$ and
$2s + 2$ (`chanWin_step2`). The windows $w_R(0), \dots, w_R(s)$ form a path, so $w_R(s)$ reaches at length $s$.

**Entry.** Reaching at length $n + 1$ implies reaching at length $n$ (drop the first window, `reach_pred`), so the sets
of windows that reach at length $n$ decrease with $n$. A window that is not in $E_W$ stops reaching at some length.
There are $2^W$ windows, so by induction on the number of windows considered there is one length $N \ge 1$ at which
every window outside $E_W$ has stopped reaching (`exists_stable`); a window that reaches at length $N \ge 1$ is a double
step, so it is below $2^W$. Then every window that reaches at length $N$ is in $E_W$, and $w_R(s)$ reaches at length
$s \ge N$, so at length $N$ (`reach_le`).

**The reduction.** Suppose $\Psi_R$ is finitely supported. It satisfies `InX` (`Psi_inX`), and its free bit at the
white step $s$ is the complement of column 1 of $R$ at the time $2s + 1$ (`Psi_free`), which is bit 0 of $w_R(s)$
(`chanWin_col1`). The windows $w_s = w_R(s)$ for $s \ge N$ are then a path in $E_W$ whose bit 0 is the complement of
the free bits of $\Psi_R$, which $\mathrm{Q01Right}(W)$ excludes. The kit's `CQ01_iff_Psi` turns this, for every
finitely supported $R$, into `CQ01`, and `Rule30PeriodTwoCoupled.no_eventual_period_two_of_CQ01` into the statement
about the center column of the single cell.

**The limit set at 14 columns.** The ranks $r(c)$, the largest $i \le 20$ with $c$ in the image of every window under
$i$ double steps, are listed as five bitmaps of $2^{14}$ bits. The kernel checks two things by `decide +kernel`:

1. for every window $c < 2^{14}$ and every input, $r(\delta_{14}(c, x_1, x_2)) \ge \min(r(c) + 1, 20)$
   (`rank14_all`, in 16 theorems of 1,024 windows each, so that no single check holds the kernel's cache for all
   16,384 windows);
2. the bitmap of the double steps of the windows of rank 20 equals the bitmap of the windows of rank 20
   (`back14_ok`).

By (1) and induction on the length, a window that reaches at length $s$ has rank at least $\min(s, 20)$
(`rank14_reach`): this gives $E_{14} \subseteq \{r = 20\}$ and the entry by step 20. By (2) every window of rank 20 is a
double step of a window of rank 20, so it reaches at every length (`inE14_reach`): this gives the other inclusion.

## What it means

$\mathrm{Q01Right}(W)$ is a statement about finite left halves alone, like the kit's `Q01` and `Q01Gap`, and it needs no
statement about the right half: the entry that the gap-trap reduction needs, every finite right half entering the gap
trap, the kit's ether family or the lock of period seven, which [the census](../../findings/period-two/gate-census.md)
checks to 20 cells and which [the residue](../../negative-results/period-two/game-residue.md) shows no forced basin at a
fixed width can prove, is replaced by entry into the limit set, which holds for every right half by finiteness of the
windows. The cost is the size of the language to absorb: column 1 along paths in $E_W$ has entropy 0.244 bit per white
step at $W = 14$ and 0.122 at $W = 28$ ([the right channel
language](../../findings/period-two/right-channel-language.md)), against 1 for `Q01`. At 14 columns neither its language nor
that of `Q01Gap` contains the other, so neither hypothesis follows from the other by inclusion of languages: the gap shift of
`Q01Gap` has entropy 0.256 ([the gap shift](../../negative-results/period-two/gap-inverse-runs.md)), above that of the
channel at 14 columns, so it is not inside it, and the channel holds words such as the alternation of the aligned
ether, which the gap shift does not. A proof of
$\mathrm{Q01Right}(W)$ at any one width excludes an eventual period two for the center column of the single cell.

## Kit

The kit's main branch reduces `CQ01` for the right halves that enter its gate trap to `Q01Gap`
(`Rule30GateTrap.not_finSupp_Psi_of_Q01Gap`, after the pinned commit), with entry as a separate hypothesis. Neither
kit tree (the pinned `lean/Ruliology/CellularAutomata/` and `equivalents/Rule30Equivalents/`, and the main branch's)
has the limit set of the windows, a reduction of `CQ01` with no entry hypothesis, or `Q01Right`. The module uses
`Psi`, `Psi_free`, `Psi_inX`, `CQ01_iff_Psi`, `no_eventual_period_two_of_CQ01`, `drv` and `stepN` from the kit.

## Reproduce

```bash
lake build Rule30Open.PeriodTwo.ChannelLanguage   # 70 to 145 s, 1.5 GB
python -m computations.right_channel_language lean --width 14   # the bitmaps of the module
```

`tests/test_right_channel_language.py` checks that the bitmaps and the rank expression of the module are those the
image chain at 14 cells gives, with the chain length 20.
