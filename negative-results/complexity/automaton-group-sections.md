---
title: The powers Φ^(2^k) of the right-edge step have minimal transducers of 3, 7, 35, 517 and 57,741 states, growing at every squaring for k ≤ 4, and Rules 90 and 150, whose cycles grow linearly, have larger ones
category: complexity
problems: [3]
status: negative
kind: dead-end
evidence: [computations/two_index.py, tests/test_two_index.py]
---

# The powers Φ^(2^k) of the right-edge step have minimal transducers of 3, 7, 35, 517 and 57,741 states, growing at every squaring for k ≤ 4, and Rules 90 and 150, whose cycles grow linearly, have larger ones

**Question.** In the frame of its right edge, one step of Rule 30 is $\Phi(x) = x \oplus (2x \lor 4x)$, a 3-state
transducer read from the least significant bit, which generates the kit's automaton group 2369
(`Rule30Equivalents.AutomatonGroup`). The cycle length $L_n$ of 1 modulo $2^n$ doubles from level $n$ to $n + 1$ exactly when
$\Phi^{L_n}(1)$ has bit $n$ set ([right-edge cycles](../../findings/complexity/right-edge-cycles.md)), that is when the
section of $\Phi^{L_n}$ reached after reading the low $n$ bits of 1 flips the next bit. If the sections of the powers
$\Phi^{2^k}$ fell into a bounded number of transducer states, as the powers of the odometer $x \mapsto x + 1$ do (the
transducer of $x \mapsto x + 2^k$ has $k + 2$ states, a counter and a carry), the doubling levels would follow a
finite recursion, and a growth law for $L_n$, the hypothesis of [TwoIndex](../../Rule30Open/Complexity/TwoIndex.md),
might be read off it. Does such a recursion exist?

**What was done.** `computations/two_index.py` squares the minimal transducer of the right-edge step repeatedly,
building the product transducer on its reachable pairs of states and minimizing it by Moore refinement, for Rule 30's
$\Phi$ and, as controls, for the right-edge steps of Rules 90 ($x \oplus 4x$) and 150 ($x \oplus 2x \oplus 4x$), whose
right-diagonal periods grow linearly and whose diagrams are 2-automatic. The test checks that each transducer computes
the power it stands for on random inputs, that Rule 30's state counts for $k \le 2$ equal the number of distinct
sections of $\Phi^{2^k}$ found by brute force (prefixes of at most 9 bits, outputs on 8 more), and that the controls
match the closed form below.

## Outcome

| $k$ | 0 | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|---:|
| Rule 30, states of $\Phi^{2^k}$ | 3 | 7 | 35 | 517 | 57,741 |
| Rules 90 and 150, states of the step to the power $2^k$ | 4 | 16 | 256 | 65,536 | ($2^{32}$) |

- **No bounded recursion on the range.** The counts for Rule 30 grow at every squaring, by factors 2.3, 5, 14.8 and
  112, so $\Phi^{2^k}$ has no description by a fixed finite set of states for $k \le 4$. This agrees with the
  classification that the kit cites, which lists group 2369 as not contracting.
- **The measure does not separate the rules.** Over GF(2), Rule 90's step is multiplication by $1 + z^2$ and Rule 150's
  by $1 + z + z^2$, so their $2^k$th powers are $x \oplus (x \ll 2^{k+1})$ and
  $x \oplus (x \ll 2^k) \oplus (x \ll 2^{k+1})$ (the Frobenius map squares each term), and a transducer for them must
  keep the last $2^{k+1}$ input bits: $2^{2^{k+1}}$ states, more than Rule 30 at every $k$ computed. Yet their cycles
  grow linearly. So a large transducer for $\Phi^{2^k}$ says nothing about the growth of $L_n$, and a small one is not
  available for Rule 30 either.

## Where it stops

The route stops at its first step. A recursion for the doubling levels through the sections of $\Phi^{2^k}$ needs those
sections to lie in a bounded set, and they do not on the range computed; the size of the transducers, the only
quantity that the failure leaves, is larger for the linear rules than for Rule 30. What decides the doubling from level
$n$ to $n + 1$ is one bit of one section, the parity of the input $R_{n-1} \lor R_{n-2}$ over a cycle, and nothing in the state
counts reaches it. The kit's own bounds on $L_n$ (`Rule30RightPeriods.period_gt`, `per_upper_half`) come from the light
cone and a record-charge count, not from the group.

**What would change this.** A finite set of states for a coarser object than $\Phi^{2^k}$, for example its action on
the orbit of 1 alone, or on residues of a fixed size, that still decides the doubling bit; or a measure of the sections
that is small for Rules 90 and 150 and grows for Rule 30.

## Reproduce

```bash
python -m computations.two_index --levels 20 --white 4 --rows 8 --kernel-e 1 --mahler 2 --transducer 4 --transducer-linear 3
```

About four seconds; the full run of `python -m computations.two_index` includes it.
