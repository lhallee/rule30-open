---
title: Crossing sequences prove at most time (log n)² for the center column, and need a spectral hypothesis that implies Problem 1
category: complexity
problems: [3, 1]
status: negative
kind: barrier
evidence: [computations/crossing_bounds.py, computations/obdd_orders.py]
---

# Crossing sequences prove at most time (log n)² for the center column, and need a spectral hypothesis that implies Problem 1

**Question.** The kit proves in Lean that a one-tape machine that decides $c(n)$ from the binary digits of $n$ in time
$o(\ell \log \ell)$, with $\ell$ the number of digits, makes $c$ 2-automatic (`OneTapeRegular`), by counting crossing
sequences. Can the same method, or a restricted model such as finite automata with several passes or ordered decision
diagrams, give a lower bound for $c$ that goes beyond that and avoids Problem 1?

**Outcome.**

1. **The first rung is Problem 1 in disguise.** By the kit, time $o(\ell \log \ell)$ is possible exactly when $c$ is
   2-automatic. A finite automaton with a bounded number of passes over the digits, one-way or two-way, deterministic or
   not, recognizes only regular languages, so it computes $c$ exactly when $c$ is 2-automatic. Each lower bound in
   these models is therefore a proof that $c$ is not 2-automatic, which implies Problem 1.
2. **A theorem, with its hypothesis.** The argument is an instance of the standard crossing-sequence, or
   communication-complexity, lower bound for one-tape machines (Hennie 1965; Kushilevitz and Nisan, *Communication
   Complexity*, 1997, chapter "Time and space", whose table of contents was checked, not its text), with a spectral
   bound of Lindsey's-lemma type on each cut; the spectral data of Rule 30 in item 4 are what this entry adds. Fix $\ell$ and a cut $i$ between cells $i - 1$ and $i$ of the input. Let $M_i$ be the
   $2^i \times 2^{\ell - 1 - i}$ matrix of signs $(-1)^{c(n)}$ for the $n$ with $\ell$ digits, rows the lowest $i$ digits $a$ and
   columns the digits $b$ between the cut and the leading 1, $n = a + 2^{\ell - 1} + 2^i b$, and $\|M_i\|$ its operator norm.
   Let a machine in the kit's model with $s$ states compute $c$ on all these $n$. Then at each cut the share of inputs
   with at most $L$ crossings is at most $(1 + s + \dots + s^L) \|M_i\|^2 / 2^{\ell - 1}$, so the mean running time over
   the $2^{\ell - 1}$ inputs is at least
   $$\sum_{i = 1}^{\ell - 1} \sum_{L \ge 0} \max\Bigl(0,\ 1 - (1 + s + \dots + s^L) \frac{\|M_i\|^2}{2^{\ell - 1}}\Bigr).$$
   If $\|M_i\|^2 \le \theta (2^{i/2} + 2^{(\ell - 1 - i)/2})^2$ for a constant $\theta$, all $\ell$ and all cuts (the
   *spectral hypothesis*), the bound is $\ell^2 / (8 \log_2 s) - O(\ell)$, a deliberately weak form of the
   $\ell^2 / (4 \log_2 s) - O(\ell)$ that the count gives, and $c$ is not 2-automatic, hence Problem 1.
3. **The method stops at $\ell^2$.** For every function the same sum is at most $\ell^2 / (4 \log_2 s) + \ell$, because a
   $\pm 1$ matrix has $\|M\|^2 \ge \max(\text{rows}, \text{columns})$. The ceiling holds for every per-cut rectangle
   bound, not only the spectral one: a single row or column of $M_i$ is a rectangle of $2^{\max(i, \ell - 1 - i)}$
   inputs, for the longer side, on which the answer is a function of one side. In terms of $n$, with $\ell = \lfloor \log_2 n \rfloor + 1$,
   the best the method can show is time of order $(\log n)^2$, exponentially below the order $n$ of the kit's `Problem3`
   and below the $n^{\varepsilon}$ of `Problem3Robust`, even for a random function.
4. **The hypothesis holds on the range computed.** For every cut of $\ell = 12, \dots, 20$ digits (the first $2^{20}$ cells), the ratio of $\|M_i\|^2$ to
   $(2^{i/2} + 2^{(\ell - 1 - i)/2})^2$ lies between 0.878 and 1.035 for the center column and between 0.881 and 1.030 for
   random signs, so $\theta = 1.04$ fits. The Thue-Morse control, which is 2-automatic, has ratios up to 176 and gives
   bound 0. The theorem's bound on the mean running time, from the same code, with $s$ states:

   | $\ell$ | center column, $s = 2$ | $s = 4$ | $s = 8$ | random signs, $s = 2$ | $\ell^2 / (8 \log_2 s)$, $s = 2$ |
   |---:|---:|---:|---:|---:|---:|
   | 12 | 13.1 | 10.1 | 8.2 | 13.3 | 18.0 |
   | 14 | 21.0 | 14.8 | 12.6 | 21.0 | 24.5 |
   | 16 | 30.4 | 21.0 | 16.9 | 30.5 | 32.0 |
   | 18 | 42.2 | 27.7 | 21.6 | 42.4 | 40.5 |
   | 20 | 56.2 | 36.2 | 28.0 | 56.1 | 50.0 |

   The bound is above the $\ell$ steps that reading the input takes only for machines with a handful of states, and
   then by a small factor; it is a certificate of the method, not a statement about machines of practical size.
5. **Ordered decision diagrams in every variable order.** The restriction of $c$ to $n < 2^{16}$ as a function of its 16
   digits has no ordered binary decision diagram, in any order of the variables, with fewer than 3,928 nodes; a
   random function gives 3,932 (one draw), and the order low digits first gives 3,976 against 3,984. At 14 digits both
   are 1,005. The parity (Thue-Morse) control needs 2. So no variable order reveals structure at these lengths.

**Proofs.**

*Lemma 1 (rectangles).* For a cut, call the states just after each crossing the crossing sequence $\sigma$ of a run. The
head starts left of the cut, so the first crossing is rightward and the side on which the run ends is fixed by the
parity of $|\sigma|$. If inputs $(a, b)$ and $(a', b')$ have the same $\sigma$, then so do $(a, b')$ and $(a', b)$: the left
half of a run is determined by $a$ and $\sigma$, the right half by $b$ and $\sigma$. So the inputs with one $\sigma$ form
a rectangle $A_\sigma \times B_\sigma$, and the answer on it is a function of $a$ alone when the run ends on the left and of
$b$ alone when it ends on the right. The kit's `OneTapeRegular.splice_word` is the same cut and paste.

*Lemma 2.* If a rectangle $A \times B$ of $M$ has the form $u \mathbf{1}^T$ (or $\mathbf{1} v^T$) with signs $u$, then
$|A||B| = u^T M \mathbf{1}_B \le \|M\| \sqrt{|A|} \sqrt{|B|}$, so $|A||B| \le \|M\|^2$.

*Counting.* At most $1 + s + \dots + s^L$ sequences have length at most $L$, each carries a rectangle of at most
$\|M_i\|^2$ inputs, which bounds the number of inputs with at most $L$ crossings at the cut. The mean number of
crossings is $\sum_{L \ge 0} \Pr[\text{crossings} > L]$. A step crosses one cut, so the running time is at least the sum of
the crossings over the cuts, and the theorem follows. Item 3: $\|M\|^2 \ge \|M\|_F^2 / \min(\text{rows}, \text{columns})
= \max(\text{rows}, \text{columns})$, so the share is at least $2^{-\min(i, \ell - 1 - i)}$ and the inner sum is empty once
$s^L$ exceeds $2^{\min(i, \ell - 1 - i)}$.

*The hypothesis gives the bound.* With $m_i = \min(i, \ell - 1 - i)$ the hypothesis gives
$\|M_i\|^2 / 2^{\ell - 1} \le 4 \theta 2^{-m_i}$, so the share is at most
$(1 + s + \dots + s^L) \cdot 4 \theta 2^{-m_i} \le 4 \theta s^{L + 1} 2^{-m_i}$. The terms are therefore at least $1/2$
for $L + 1 \le (m_i - 3 - \log_2 \theta) / \log_2 s$, and $\sum_i m_i \approx \ell^2 / 4$, which gives
$\ell^2 / (8 \log_2 s) - O(\ell)$. Counting each term as $1 - 4 \theta s^{L + 1} 2^{-m_i}$ instead, the subtracted
parts form a geometric sum at most $s / (s - 1) \le 2$ per cut, which gives $\ell^2 / (4 \log_2 s) - O(\ell)$.

*The hypothesis gives Problem 1.* If $c$ is 2-automatic with a 2-kernel of $r$ sequences, the rows of every $M_i$ are
restrictions of kernel members, so $M_i$ has rank at most $r$, and $\|M_i\|^2 \ge \|M_i\|_F^2 / r = 2^{\ell - 1} / r$. The
hypothesis gives $\|M_i\|^2 \le 4 \theta 2^{\ell - 1 - m_i}$, so $r \ge 2^{m_i} / (4 \theta)$ for every $\ell$, which is
impossible. The kit proves that an eventually periodic sequence is 2-automatic.

*Ordered decision diagrams.* A diagram that reads the variables in the order $p$ has at least as many nodes as the
function has distinct subfunctions after the first $j$ variables are fixed, for each $j$; the least largest such count
over all orders is found by a dynamic program over subsets ([computations/obdd_orders.py](../../computations/obdd_orders.py)),
checked against all $6! = 720$ orders for 6 variables.

**What it means.** Restricted models do not give a way around Problem 1: each lower bound in a finite-state model is a
proof of non-automaticity, and the spectral hypothesis, the only form in which the stronger crossing-sequence method
could apply to $c$, implies it too. What the hypothesis would give is a lower bound of order $(\log n)^2$, which is
not the order $n$ that the prize asks about. The data do not distinguish $c$ from random signs at these lengths, so
there is no sign of the structure that a shortcut would need, in the same sense as [the automaton
search](automaton-lower-bounds.md), whose distinct-block counts bound the ranks used here from above. The theorem is
argued on paper, and a Lean proof would need the operator norm over the reals, which the kit's equivalent forms do not
use.

**What would change this.** A proof that $\|M_i\|^2 \le 2^{\ell - 1 - \delta \min(i, \ell - 1 - i)}$ for some $\delta > 0$
(it implies Problem 1 and the bound above); or a lower-bound method for one tape that is not a sum of per-cut counts.

**Reproduce.**

```bash
python -m computations.crossing_bounds --min-ell 12 --max-ell 20
python -m computations.obdd_orders 16
```

The tests `tests/test_crossing_bounds.py` and `tests/test_obdd_orders.py` check Lemmas 1 and 2 on random machines
(every group of inputs with one crossing sequence is a rectangle, and the count never exceeds the bound), the controls,
and the dynamic program against all orders.
