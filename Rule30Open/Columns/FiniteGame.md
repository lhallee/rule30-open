---
title: A finite game rules out repeating blocks
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.FiniteGame
headline: [game_column, center_not_01111111, center_not_00000011]
kit: independent
kit_modules: [Rule30StripCertificates]
evidence: [computations/game.py]
---

# A finite game rules out repeating blocks

Suppose a column repeats a block $w$ forever. The cells right of it are then driven by a known periodic input, and
whatever happens far to the right reaches them only through one unknown cell per step. Treating that cell as an
adversary turns the question into a finite game. When a certificate shows that every play makes the column on the
left eventually periodic, the adjacent-column theorem excludes $w$. Two certificates are checked here, for $01^7$ and
$0^61^2$.

## Statement

- `game_column`: in the orbit of a row with a leftmost 1, no column repeats a block that has a certificate passing
  `GameCert.check`, from any time and in any rotation.
- `center_not_01111111`, `center_not_00000011`: the center column does not eventually repeat $01111111$ or
  $00000011$, in any rotation.

## Argument

Let column $k$ follow $w$ of length $P$ from time $T$, so $a_t(k) = w_{(t + s) \bmod P}$ for a shift $s$.

1. **The game.** Keep the $K$ cells $k + 1, \dots, k + K$. One step updates them from the column value on the left,
   the cells themselves and cell $k + K + 1$ on the right. A node is a pair (phase, cells), $P \cdot 2^K$ nodes in all,
   and a move from a node goes to the next phase and the cells after one step, for either value of the free cell. The
   real row is one play: its cells follow a move at every step, with the free cell set to the real one
   (`game_cells`).
2. **What the node shows.** By left permutivity, column $k - 1$ at time $t$ is
   $w_{\varphi + 1} \oplus (w_\varphi \lor \text{first cell})$, a function of the node at time $t$ (`leftValue`).
3. **The certificate.** It assigns every node a rank below 256, marks some ranks transient, and gives a value
   $v(\rho, \varphi)$ for every other rank $\rho$ and phase $\varphi$. `GameCert.check` verifies, at every node and for
   both values of the free cell, that a move never lowers the rank, that a move from a transient rank raises it, and
   that at a rank that is not transient, column $k - 1$ read off the node equals $v(\rho, \varphi)$.
4. **The play settles.** Along the real play the rank never falls and stays below 256, so it is constant from some
   time $t_1$ on (`settles`). That constant rank is not transient, since a move from a transient rank would raise it.
   So from $t_1$ on, column $k - 1$ equals $v(\rho, \text{phase})$, which repeats with period $P$. Columns $k - 1$ and
   $k$ are both eventually periodic, against [the adjacent-column theorem](AdjacentColumns.md).

## How the certificates are found

[computations/game.py](../../computations/game.py) builds the game graph and its strongly connected components. A play
ends inside one component, and only components with an internal move can hold a play forever. If in each of those
column $k - 1$ is a function of the phase, ranking nodes by their component's depth in the condensation, with the
components that can hold a play kept apart, gives a certificate. The block $01111111$ has one at $K = 5$ and
$00000011$ at $K = 6$. The construction fails for $01$ at every width tried: some component that can hold a play
shows column $k - 1$ taking both values at one phase. Over every primitive block of period up to 14 the game excludes
76 of 2,538 (see [the game blocks finding](../../findings/columns/game-blocks.md)), and
[the game in bit masks](GameBlocks.md) checks 32 of them that the kit does not exclude.

## In Lean

The certificate is packed in three numbers (`ranks`, `transient`, `values`) so that `GameCert.check` runs in the kernel
by `decide +kernel` (`cert01111111_check`, `cert00000011_check`). `single_not_01111111` and `single_not_00000011` cover
every column of the single cell's orbit.

## Relation to the kit

The kit excludes both blocks with certificates of its own:
[`Rule30StripCertificates`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30StripCertificates.lean)
has `not_eventually_01111111` (a bit-mask strip certificate of width 5) and `not_eventually_00000011` (a rank
certificate of width 6 with 379 ranks). The kit reads column 1 at the white times of the center and applies masked
Jen; this game reads column $k - 1$ at every time and applies the adjacent-column theorem, and it covers every column
of every row with a leftmost 1. These are independent proofs.
