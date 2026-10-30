---
title: Every window can reach the period-four certificate, so a fair coin beyond it locks the right half
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/coin_lock.py]
---

# Every window can reach the period-four certificate, so a fair coin beyond it locks the right half

Take the certificate of [the certificate finding](period-four-certificate.md) for a period-four word $w$: the windows
of columns 1 to $W$ that the driven rule never leaves, whatever column $W + 1$ does, and on which column 1 at the white
times is fixed. Whether a run enters it depends only on what column $W + 1$ does, and entry is forced whatever that
cell does from only 2.5% to 42.5% of the windows, by word, width and phase. This finding asks the opposite question,
whether some values of column $W + 1$ lead in, and compares a fair coin there with Rule 30 itself.

- **No window is a trap.** For $0001$, $0011$ and $0111$ at $W = 16$ and $18$, and for $0011$ and $0111$ at $W = 14$,
  every window at every phase enters the certificate for some sequence of values of column $W + 1$, within at most 80
  steps.
- **One word serves every window.** At $W = 16$ a single sequence $u_w$ of 425, 697 or 297 values of column 17 (for
  $0001$, $0011$, $0111$) brings every window at phase 0 into the certificate. A right half driven by $w$ therefore
  locks for good once its column 17 reads $u_w$ from a time divisible by 4; the lock can fail only for halves whose
  column 17 never does.
- **A fair coin locks.** With column 17 a fair coin flipped at every step, every window enters with probability 1.
  The expected entry time is at most 1,144, 688 and 140 steps, and 111.5, 95.7 and 49.8 on average over the windows at
  phase 0. The chance of still being out falls by a factor 0.99898, 0.99782 and 0.98251 per step, and after 12,000
  steps it is at most $6.3 \times 10^{-6}$, $7.8 \times 10^{-10}$ and $7.6 \times 10^{-92}$, from every window.
- **Rule 30 is not a fair coin there.** Of 1,000 right halves in Rule 30 itself, the empty one and 999 random halves of
  64 cells (the first 31 are the starts of [the locking finding](period-four-locking.md)), 71, 26 and 28 stay out of the
  certificate for all 12,000 steps; the rest enter by step 550, 1,019 and 325 (median 66, 53 and 33). Every half that
  stays out enters the kit's ether-and-wall family, by step 274, 392 and 191, so it locks too: through an ether plug
  deeper than a window of 16 columns holds, as [the absorption census](absorption-census.md) found for its starts.

## What it means

The lock has a probabilistic form that is true: no window blocks it, and a generic column 17 completes it. The
deterministic lock needs more, because Rule 30's own right half is not generic beside a periodic center. A few percent
of random starts stay out by building ether plugs, an outcome the coin model gives a chance below $10^{-5}$, and those
runs stay off the entry paths for all 12,000 steps. They lock anyway, so the plugs are no counterexample; but they
show that attraction, the open part of [the locking conjecture](period-four-locking.md), cannot follow from treating
the far right half as random. It needs the structure that the kit's family describes, with an ether prefix of any
length. [The negative result on random rows](../../negative-results/random-rows/almost-every-row.md) records the same
gap for the prize problems themselves.

## Method

Windows, phases and the certificate are those of [the certificate finding](period-four-certificate.md), with the `jen`
seed: the union, over the values of column 1 at the white phases, of the greatest invariant families.
[computations/coin_lock.py](../../computations/coin_lock.py) computes, on the $4 \cdot 2^W$ pairs of window and phase:

- `entry_paths`: the least number of steps to enter with column $W + 1$ chosen freely, by backward search from the
  certificate, and a first value on a shortest path;
- `universal_word`: from all $2^W$ windows at phase 0, repeatedly follow a shortest path of the closest window not yet
  inside, moving every window along. The certificate keeps every window it holds, so each round brings at least one
  more window in. The words are found greedily and need not be the shortest;
- `expected_entry`, by value iteration of $h = 1 + \tfrac12\,(h(s_0) + h(s_1))$ outside the certificate, with $s_b$
  the successor when column $W + 1$ reads $b$; `decay_rate`, by power iteration of one period of the chance of staying
  out; and `stay_out`, that chance after 12,000 steps, by exact recursion over the steps;
- `sample`: entry of Rule 30's own right halves into the certificate within 12,000 steps
  (`lock_certificate.entry_time`), and of those that stay out into the kit's family within 4,000 steps
  (`absorption.absorb`).

`tests/test_computations.py` checks the search, the word, the expected times and the decay against integer-row and
bool-array evolution, and against simulated runs, and checks that among the 31 starts of the locking finding exactly
the ones the certificate finding names stay out (start 4 under $0001$, 24 under $0011$, 8 and 18 under $0111$).

## Formalization

The first two items are finite statements, checkable like the kit's strip certificates: a table of distances on
$4 \cdot 2^{16}$ pairs, or the word $u_w$ run on every window. The coin model's numbers are floating-point.
[LockWord](../../Rule30Open/Columns/LockWord.md) proves the second item's form in Lean with the kit's ether-and-wall
family in place of this certificate: one sequence in column 17, 15 or 14 brings every window, from every start phase,
into the family, so a center that repeats the word keeps that column off the sequence forever.

## Reproduce

```bash
python -m computations.coin_lock 0001 0011 0111 --widths 14 16 18
python -m computations.coin_lock 0001 0011 0111 --widths --chain-width 16 --samples 1000
```

The first takes about 20 s; the second about 6 min, most of it in the expected entry time of $0001$ and the
sample.
