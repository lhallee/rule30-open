---
title: A lock of period seven beside an alternating center excludes period two for every right half that enters it
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.SevenLock
headline: [sevenLock_check, sevenLock_forever, sevenLock_periodic, sevenLock_not_finSupp_Psi, no_alternating_of_sevenLock, no_alternating_sevenLock_example]
kit: new
kit_modules: [Rule30PeriodTwoSideways, Rule30Ether, Rule30StripCertificates, Rule30EtherThreeReach]
evidence: [computations/gate_census.py]
---

# A lock of period seven beside an alternating center excludes period two for every right half that enters it

Drive a right half with an alternating center, black at the even steps. A set of 195 windows of the columns 1 to 32
is closed under the rule whatever the cells beyond column 32 hold, and inside it column 1 repeats $0101000$ at the
white steps. A right half that enters it leaves column 1 periodic, so by the kit's absorption route no finite left
half keeps the center alternating against it. This excludes period two outright, with no open hypothesis, for every
finite configuration whose right half ever reaches the lock, whatever its left half and whatever its right half holds
beyond column 32.

## Statement

Write $u_R(s)$ for column 1 at the white step $2s + 1$ of the right half $R$ driven by the center $1, 0, 1, 0, \dots$
(the kit's `u R`), and $\Psi_R$ for the one left half that keeps the center alternating against $R$ (the kit's
`Psi R`). A window is the list of columns 1 to 32 at a step, coded as a 32-bit number, bit $i$ for column $i + 1$.

- `sevenLock_check`: the lock, seven classes $C_0, \dots, C_6$ of 22, 22, 24, 34, 37, 32 and 24 windows. Every window of
  $C_k$ reads `lockWord k` in column 1, the $k$-th letter of $0101000$, and two steps later, for each of the four
  values that column 33 can hold at the two steps, it is a window of $C_{k+1 \bmod 7}$. The kernel checks this.
- `sevenLock_forever`: if the window of $R$ at an odd step $t_0$ is in $C_k$, then the window at $t_0 + 2n$ is in
  $C_{k + n \bmod 7}$ for every $n$.
- `sevenLock_periodic`: then $u_R(s_0 + n)$ is the letter $k + n \bmod 7$ of $0101000$, where $t_0 = 2s_0 + 1$, so
  $u_R$ is eventually periodic with period 7.
- `sevenLock_not_finSupp_Psi`: then $\Psi_R$ has infinitely many black cells.
- `no_alternating_of_sevenLock`: no finite configuration whose center reads $1, 0, 1, 0, \dots$ from time 0 has its columns
  1 to 32 in the lock at an odd step.
- `no_alternating_sevenLock_example`: no finite configuration whose cells $1, 2, \dots$ read $1\,0\,0\,1\,0\,1\,1\,1\,1$
  and then only white keeps its center alternating from time 0, whatever its left half; its columns enter $C_4$ at
  step 29 (`example_enters`).

## Argument

1. **The double step** (`win_step2`). From an odd step the center is white and then black, so the window two steps
   later is $\mathrm{lin3}(1 :: \mathrm{lin3}(0 :: w \mathbin{+\!\!+} [x_1]) \mathbin{+\!\!+} [x_2])$, where $w$ is the
   window and $x_1, x_2$ are column 33 at the two steps; the window does not determine them. This is the kit's
   `rowOf_succ` applied twice.
2. **Closure** (`lock_ok`, `win_lock_forever`). The check runs over the 195 windows and the four values of
   $(x_1, x_2)$, decoding each code with `decode` and recognizing the image by its code (`seg_encList`,
   `decode_encList`). By induction on $n$ the window stays in the lock and moves one class per double step, whatever
   the cells beyond column 32 do.
3. **Column 1** (`u_of_lock`, `u_periodic_of_lock`). Column 1 is the head of the window, so at the white step
   $t_0 + 2n$ it is the letter of the class, and $u_R(s + 7) = u_R(s)$ for every $s \ge s_0$.
4. **The left half** (`not_finSupp_Psi_of_lock`). The free bits of $\Psi_R$ are the complement of $u_R$, and the free
   bits of a finitely supported constrained start are never eventually periodic (the kit's
   `not_finSupp_Psi_of_eventuallyPeriodic`, from `free_not_eventuallyPeriodic`).
5. **Finite configurations** (`no_alternating_of_lock`). If a finite configuration keeps the center alternating, its
   left half is constrained and coupled to its right half (the kit's `left_inX` and `left_coupled`), so it equals
   $\Psi_R$ at every depth from 1 (`Psi_unique`) and has finitely many black cells, against step 4. Its columns
   1 to 32 are the window of the driven right half (`right_is_drv`).
6. **The example** (`no_alternating_lock_example`). The row of the example at step 29 is computed as a number by the
   kit's `rowN` (`rowN_eq_drv`), its window is in $C_4$ by `decide +kernel`, and any configuration whose right half
   agrees with the example has the same driven right half (`drv_congr`).

## Where the lock comes from, and what it covers

The lock is the closure, under every input from the right, of the windows that the half $0101001$ (cells 2, 4 and 7
black) shows from about step 380 on, when columns 1 to 25 have become periodic with period 14 and a growing stripe
domain separates them from the chaotic cells beyond
(`python -m computations.gate_census lock`). At widths 26, 28 and 30 the closure of those windows has about 0.26,
0.62 and 1.5 million windows; at width 32 it closes at 195.

Beside an alternating center every right half of up to 16 cells, in both phases, enters one of three closed sets: the
lock, the kit's ether-and-wall family, on which column 1 is periodic as well, or a gap trap, on which the black cells
of column 1 come 3 or 5 white steps apart, the setting of the kit's open `Q01Gap`
([the census](../../findings/period-two/gate-census.md)). About one half in a hundred of up to 16 cells enters the
lock, and the lock catches halves that neither the kit's family nor its gate trap does.

## Relation to the kit

The kit's `Rule30PeriodTwoSideways` gives the absorption route (`not_finSupp_Psi_of_eventuallyPeriodic`) and the
reduction of finite configurations to $\Psi_R$; its ether-and-wall family (`Rule30Ether`) is a different set on which
column 1 is periodic, with period 4 in time, and its `Rule30GateTrap`, on its main branch after the commit pinned
here, is the gap trap. This lock, with column 1 of period 14 in time, is not in the kit. The double step and the codes
follow the gate trap's (`step2`, `decode`), at width 32.

## Lean

`Rule30Open.PeriodTwo.SevenLock`: `win`, `step2`, `allSucc`, `win_length`, `win_step2`, `allSucc_spec`, `decode`,
`testBit_encList_zero`, `testBit_encList_succ`, `seg_encList`, `decode_encList`, `lockWord`, `lockCls`, `inCls`,
`lockCheck`, `lock_ok`, `lock_spec`, `lockCls_empty`, `inCls_spec`, `win_lock_forever`, `win_head`, `u_of_lock`,
`u_periodic_of_lock`, `not_finSupp_Psi_of_lock`, `no_alternating_of_lock`, `exampleHalf`, `exampleWindow`,
`exampleWindow_inCls`, `example_enters`, `no_alternating_lock_example`. The module elaborates in about 20 seconds.
`python -m computations.gate_census lean` writes the classes as the file lists them.
