---
title: The light-like map of Rule 30 has one preimage after every 010, so it is invertible almost everywhere and not exact, and no right diagonal of any space-time diagram reads 00100 or 11011
category: random-rows
problems: [2]
status: proved
lean: Rule30Open.RandomRows.LightLine
headline: [LightLine.eq_true_of_window, LightLine.eq_of_light_eq_of_window, LightLine.eq_of_light_eq_of_frequently, LightLine.lightIter_cell, LightLine.lightLine_avoids, LightLine.diag_avoids]
kit: refines
kit_modules: [Rule30Equivalents.Preimages, Rule30Equivalents.Mixing]
---

# The light-like map of Rule 30 has one preimage after every 010, so it is invertible almost everywhere and not exact, and no right diagonal of any space-time diagram reads 00100 or 11011

The light-like map $G = \sigma F$, $(Gy)_i = y_i \oplus (y_{i+1} \lor y_{i+2})$, is Rule 30 in the frame that moves one
cell right per step. It reads only the cell itself and the cells to its right, so it acts on the half-lines
$X_0 = \{0,1\}^{\mathbb{N}}$, and it preserves the uniform measure $\lambda$ there. Its light lines
$t \mapsto (G^t y)_j$ are Rule 30's right diagonals. This module proves two facts about them that hold for every row.

## Statement

1. **One preimage after `010`** (`eq_true_of_window`, `eq_of_light_eq_of_window`,
   `eq_of_light_eq_of_frequently`). If $Gy$ reads $0\,1\,0$ at $q, q+1, q+2$, then $y_q = 1$, and any $y'$ with
   $Gy' = Gy$ agrees with $y$ on the cells $0, \dots, q$. So two half-lines with the same image are equal when the
   image shows $010$ arbitrarily far to the right.
2. **Right diagonals** (`lightIter_cell`). For the half-line $u_j = x^t_{i+j}$ cut from row $t$ of any Rule 30
   diagram $x$, the cell $j$ of $G^r u$ is $x^{t+r}_{i+r+j}$.
3. **No right diagonal reads `00100` or `11011`** (`lightLine_avoids`, `diag_avoids`). For every row, time $t$ and
   cell $i$, the cells $x^{t+r}_{i+r}$, $r = 0, \dots, 4$, never read $b\,b\,\bar b\,b\,b$.

## Consequences (paper)

- **$G$ is invertible almost everywhere, hence not exact.** $\lambda$-almost every $z \in X_0$ shows $010$
  arbitrarily far to the right (Borel's normal number theorem, the kit's `RandomConfigurations.ae_isNormal` with
  `Mixing.exists_ge_of_disjunctive`), and every $z$ has a preimage (the block map is onto, and a decreasing sequence of
  nonempty closed sets of preimages of longer and longer prefixes has a point in common). So $G$ is a bijection of a
  set of full measure onto a set of full measure, and the inverse $\psi(z)_i$, the value that the first $010$ of $z$
  at or right of $i$ forces, is Borel. Then $G^{-1}\mathcal{B} = \mathcal{B}$ modulo $\lambda$, so
  $\bigcap_n G^{-n}\mathcal{B} = \mathcal{B}$ is not trivial: **$(X_0, G, \lambda)$ is not exact**, and it is its own
  natural extension. The ergodic questions that remain for it are those of an invertible map: ergodicity, mixing,
  the K property and Bernoullicity ([light-like mixing](../../findings/random-rows/lightlike-mixing.md)).
- **No light line is normal.** Under $\lambda$ each cell of a light line is a fair coin, but by item 3 no light line of
  any row contains $00100$. Exhaustive evolution finds exactly 30 of the 32 words of length 5 in light lines, and
  the exact law of the letter process gives 100,592 of the $2^{20}$ words of length 20, so the language of light lines
  has topological entropy at most $\frac{1}{20}\log_2 100{,}592 = 0.831$ bits per step
  ([light_line.py](../../computations/light_line.py)). The kit proves that every line of velocity other than 1 is
  normal for almost every row (`Mixing.ae_isNormal_lines`); velocity 1 fails for every row.

## Argument

1. **`010` forces a black cell.** With $z = Gy$: $z_{q+2} = 0$ gives $y_{q+2} = y_{q+3} \lor y_{q+4}$; $z_{q+1} = 1$
   gives $y_{q+1} = \lnot(y_{q+2} \lor y_{q+3})$; $z_q = 0$ gives $y_q = y_{q+1} \lor y_{q+2}$. If $y_{q+2} = 1$, then
   $y_q = 1$. If $y_{q+2} = 0$, then $y_{q+3} = 0$, so $y_{q+1} = 1$ and $y_q = 1$. The Lean proof runs the 32 cases.
2. **The cells left of it follow.** $y_{q-1} = z_{q-1} \oplus (y_q \lor y_{q+1}) = \lnot z_{q-1}$, and from two adjacent
   known cells the left-permutive step $y_i = z_i \oplus (y_{i+1} \lor y_{i+2})$ fixes every cell further left
   (`eq_of_light_eq_down`). The kit's `Preimages.eq_of_evol_one_eq_of_frequently` is the same argument for $F$ on
   two-sided rows; here it is the half-line version.
3. **Right diagonals.** By induction on $r$: $G$ applies Rule 30 at the cell one step to the right, which is the
   definition of `evolve`.
4. **The forbidden word.** The cells $(G^r y)_0$, $r \le 4$, depend on $y_0, \dots, y_8$; the kernel checks all 1,024
   cases (with the bit $b$). By hand: a constant pair $c_t = c_{t+1}$ needs $c^1_t = c^2_t = 0$ on the next two lines;
   then the flips at $t + 1$ and $t + 2$ and a second constant pair at $t + 3$ contradict the rule on lines 1 to 3.

## What the kit has

The kit proves that $F$ is invertible almost everywhere on two-sided rows (`Mixing.ae_existsUnique_preimage`, from
`Preimages.eq_of_evol_one_eq_of_frequently`), that right diagonals are not fair coins at lag 1
(`Mixing.measure_diag_eq`: neighbors agree with probability $1/4$), and that every right diagonal of the single seed
is periodic (`Rule30Diagonals.R_periodic`). The half-line version of the preimage argument, its consequence that $G$
is not exact, and the forbidden words of right diagonals are not in the kit or this repository.
