---
title: The center cell is a random-looking polynomial
category: structure
problems: [3]
status: negative
kind: no-signal
evidence: [computations/algebra.py]
---

# The center cell is a random-looking polynomial

**Question.** As a polynomial over GF(2) in the initial cells, is the center cell sparse or of low degree in some
window, which could give a shortcut?

**Outcome.**

- In the full backward cone the degree is exactly $2t - 1$ ([the degree finding](../../findings/structure/center-degree.md)),
  and the number of monomials grows from 30 at $t = 3$ to 87,887,332 at $t = 14$.
- In a fixed window of initial cells $[-w, w]$ (cells outside held at 0), with $n = 2w + 1$ variables, the number of
  monomials reaches $2^{n-1}$, the size of a random function of $n$ variables, by about $t = 10$, and stays there to
  $t = 1{,}024$ ($w = 8$: 65,785 of 131,072 possible), with degree $n$ or $n - 1$.
- The period-two constraints, written as polynomials in the free cells of the left half
  ([HeldColumn.md](../../Rule30Open/PeriodTwo/HeldColumn.md)), have term counts 2, 1, 2, 1, 4, 5, 6, 7, 10, 15, 18,
  29, 24, 59, 62, 93, 102, 207, 238, 417, 444, 845 and 842 over the first 23 constraints, and degree about half the
  constraint's index: no sparse or low-degree structure.

**What it means.** No algebraic shortcut of the sparse or low-degree kind exists in these windows. High degree alone
does not prove hardness, since a dense polynomial can still be cheap to evaluate on one input.

**Reproduce.** [computations/algebra.py](../../computations/algebra.py) computes the cone polynomials for small $t$;
the window and constraint counts came from code that is not in this repository.
