---
title: Windows of 5, 8, 10 and 12 cells at the top of a defect on the ether do not bound it, with or without the condition of K
category: period-two
problems: [1]
status: negative
kind: barrier
evidence: [computations/held_shift.py, computations/background_halves.py]
---

# Windows of 5, 8, 10 and 12 cells at the top of a defect on the ether do not bound it, with or without the condition of K

**Idea.** Conjecture (R) of [the shift model](../../findings/period-two/shift-model.md) says that every rational point
of $K$ has an eventually periodic itinerary. For a point whose tail is the ether, item 5 there reduces this to a bounded
top of the defect, the highest cell where $H^t(U)$ differs from the ether. The idea is to bound the top by a finite
object that follows the cells next to it: an automaton on a window at the top, a strip below the top that the rule
keeps, or either one strengthened by the condition of $K$ (bit 0 of $H^t(U)$ is 1 at every odd $t$).

**Where it stops.** The window automaton at 5, 8, 10 and 12 cells has a certified cycle of positive gain,
no strip of 12 cells or fewer is closed, and the condition of $K$ at a fixed lag changes no transition.

- **The window automaton has a cycle of positive gain.** `front_rate` follows the top and the 7 cells below it
  exactly and treats the cells below as free. Its longest walk of 20,000 steps gains 4,381. A walk splits into a
  simple path and cycles; no edge gains more than 1, so a walk with no cycle of positive gain gains at most 3,587, one
  less than the 3,588 nodes. So the automaton lets the top rise without limit (`--front 8 --rounds 20000`). The same
  certificate holds at window 5, where 2,500 steps gain 706 on 452 nodes. At window 10, 90,000 steps gain
  15,757 on 14,340 nodes (`--front 10 --rounds 90000`, about 40 s), and at window 12,
  400,000 steps gain 63,643 on 57,348 nodes (`--front 12 --rounds 400000`, about 12 minutes on one core). Every
  window below the 13 cells of the closed strips therefore lets the top rise without limit.
- **No narrow strip below the top is closed.** By the mirror that turns $H$ into Rule 30, a strip of cells just below
  the top on the ether of $H$ is a strip right of a column of the ether of Rule 30. `background_halves.wall_set` finds
  no set of such strips that the rule keeps for every input from beyond at widths 1 to 12, beside any of the 7 columns.
  At width 13 the greatest set has 605, 433, 533 and 344 strips at the four phases, 1,915 in all, beside one column,
  and its terminal component is the kit's 109 wall states (`absorption.kit_wall`). A top that enters this set
  stays bounded for every head, without the condition of $K$. Entry is sufficient, not necessary: a top can stay
  bounded under its actual input from below without lying in a set closed under every input.
- **The condition of $K$ is invisible at a bounded lag** (proved in Lean,
  [BoundedLag](../../Rule30Open/PeriodTwo/BoundedLag.md)). For every 2-adic $Y$, every $s \ge 0$, every
  $m \ge 1$ and every prescription of bit 0 of $H^t(U)$ at the times $t < s + m$, some 2-adic $U$ has $H^s(U)$ equal to
  $Y$ on every cell $j \ge m$ and meets the prescription; $U$ is rational when $Y$ is. Bit 0 of $H^t(X)$ is $x_t$
  plus a function of $x_0, \ldots, x_{t-1}$ (item 1 of the shift model), so choosing $x_0, \ldots, x_{m-1}$ in turn,
  with $x_j = y_j$ for $j \ge m$, sets bit 0 at the times $s$ to $s + m - 1$. $H$ is onto and two to one: a preimage of
  $h$ is fixed by its cell 0 through $u_{j+1} = h_j \oplus (u_j \lor u_{j-1})$, and that cell 0 is bit 0 at the
  earlier time. Pulling $X$ back $s$ steps sets the times 0 to $s - 1$. So an automaton that reads a window at or
  above cell $m$, treats the cells below as free and checks the condition of $K$ only before time $s + m$ has the same
  transitions with and without it. A running front raises the top past any fixed lag, so a window automaton strengthened
  by $K$ at a fixed lag fails exactly as the one without it.

**What it means.** For ether tails, what (R) still needs is that the top of every defect stays bounded, and the
natural sufficient form of that is entry into the closed strips of width 13. That form uses no condition of $K$ and
is the mirror, in $H$, of the kit's open `Absorption` conjecture for the ether, so this route turns (R) on ether tails
into a problem of the same kind as the kit's, not into an easier one. A proof that uses $K$ has to use it at a lag that
grows with the top, through the identities between the ether cells above the top and the forced bits below, which are
dense polynomials ([the forced bits](forced-bits-dense.md)). Over every head of 6 bits, most of them outside $K$, no defect top passes $p + 27$ in 1,500 steps (item 8 of the
shift model, `--ether 6`), and the ether-tail points of $K$ found in item 7 are preperiodic, so their tops are bounded;
the stall is therefore not evidence that $K$ matters here.

**Reproduce.**

```bash
python -m computations.held_shift --front 8 --rounds 20000
python -m computations.held_shift --front 10 --rounds 90000
python -m computations.background_halves 4 --walls 13
```

The first and last take a few seconds, the second about 40 s. `tests/test_held_shift.py` checks the certificate at window 5, and
`tests/test_background_halves.py` checks the sizes of `wall_set` beside the ether against those of the kit's greatest
wall and, on a sample, against a closure computed cell by cell.
