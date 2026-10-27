---
title: No automaton with fewer than 131,070 states computes the column from the digits of t
category: complexity
problems: [3]
status: negative
kind: no-signal
---

# No automaton with fewer than 131,070 states computes the column from the digits of t

**Question.** Is the center column $k$-automatic for some small automaton, which would give a fast algorithm for cell
$t$ (a negative answer to Problem 3)?

**Method.** Exact lower bounds that hold for every automaton agreeing with the first $2^{22}$ cells. Reading $t$ most
significant digit first, an automaton is in one state after the digits of $a$, so the number of distinct blocks
$(c(ak^L + v))_{v < k^L}$ bounds its states from below. Reading least significant digit first, it is in one state after
the $e$ lowest digits $r$, so the number of distinct kernel subsequences $(c(k^e n + r))_{n \ge 1}$ bounds it.

**Outcome.**

| Base, digit order | Center column | ChaCha20 | Most the data can show |
|---|---:|---:|---|
| 2, most significant first | 131,070 | 131,068 | about $N/32$ |
| 2, least significant first | 65,535 | 65,535 | 65,535 |
| 3, most significant first | 155,262 | 155,272 | about $N/27$ |
| 3, least significant first | 88,573 | 88,573 | 88,573 |
| 4, most significant first | 65,535 | 65,535 | about $N/64$ |
| 4, least significant first | 21,845 | 21,845 | 21,845 |

The same bounds give 2 to 104 states for the 2-automatic controls in bases 2 and 4, and they fail in base 3 as
Cobham's theorem predicts. The 2-kernel of the column also has full rank over GF(2) at every level tested (levels up to
9, rows up to length 1,088).

**What it means.** Every automaton that computes the first $2^{22}$ cells has at least as many states as the data can
reveal, exactly as for a cryptographic keystream. It excludes automatic structure, not other fast algorithms: two
linear feedback shift registers with $O(\log t)$ algorithms give the same maximal bounds.

**Evidence.** Quoted from code that is not in this repository.
