# Computations

Each module reproduces the numbers that one or more entries quote, runs as `python -m computations.<module>` from the
repository root, and is checked by [tests/test_computations.py](../tests/test_computations.py). They need NumPy, SciPy
and tqdm, and run on a laptop.

| Module | Reproduces | Command | Time |
|---|---|---|---|
| [rule30.py](rule30.py) | The center column and small spacetime diagrams | (library) | |
| [game.py](game.py) | [The finite game](../Rule30Open/Columns/FiniteGame.md)'s certificates and [their bit-mask form](../Rule30Open/Columns/GameBlocks.md) ([to period 16](../Rule30Open/Columns/GameBlocksLong.md)), [the 197 excluded blocks](../findings/columns/game-blocks.md) with the 136 the kit lacks, and [Jen's theorem on farther columns](../negative-results/columns/jen-farther-columns.md) | `python -m computations.game --max-period 16` | 20 min |
| [right_half.py](right_half.py) | [Period-four locking](../findings/columns/period-four-locking.md) and [the right channel](../findings/period-two/right-channel.md) | `python -m computations.right_half 12000 30 --max-period 7` | 15 s |
| [lock_certificate.py](lock_certificate.py) | [The period-four certificate](../findings/columns/period-four-certificate.md) | `python -m computations.lock_certificate 0001 --widths 14 16 --steps 20000` | 5 s |
| [coin_lock.py](coin_lock.py) | [A fair coin beyond the period-four certificate](../findings/columns/coin-lock.md) | `python -m computations.coin_lock 0001 0011 0111 --widths 14 16 18` | 17 s |
| [slow_halves.py](slow_halves.py) | [The slow-half searches](../negative-results/columns/slow-half-search.md) | `python -m computations.slow_halves 0001 0011 0111 --beam 512 --start 12 --stop 64 --steps 8000` | 80 s |
| [ether_prefix.py](ether_prefix.py) | [Truncated ether](../Rule30Open/Columns/EtherPrefix.md) | `python -m computations.ether_prefix --tail 4` | 2 min |
| [long_window.py](long_window.py) | [The 65,536-cell window](../Rule30Open/Columns/LongWindow.md) | `python -m computations.long_window` | 1 s |
| [period_three.py](period_three.py) | [The word 011 does not settle](../negative-results/columns/period-three-011.md) and [entry into the trap for 001](../findings/columns/t001-census.md) | `python -m computations.period_three --trap --cells 10 --steps 400000` | 8 min |
| [small_halves.py](small_halves.py) | [Ten cells](../Rule30Open/Columns/TenCells.md) | `python -m computations.small_halves --cells 10` | 30 s |
| [sparse_halves.py](sparse_halves.py) | [Sparse right halves](../Rule30Open/Columns/SparseRight.md) | `python -m computations.sparse_halves` | 30 s |
| [periodic_columns.py](periodic_columns.py) | [Columns that repeat from time 0](../negative-results/columns/periodic-from-start.md) | `python -m computations.periodic_columns --cells 20 --max-period 32 --steps 256` | 15 s |
| [wall_segments.py](wall_segments.py) | [The segments that keep the cell beside a column known after nine 1s](../Rule30Open/Columns/WallSegments.md), with three values and [with sets of windows](../Rule30Open/Columns/WallSets.md), and [how long a stripe keeps it](../Rule30Open/Columns/WideWall.md) | `python -m computations.wall_segments --max-period 22` | 50 s |
| [held_map.py](held_map.py) | [The period-two integer map](../findings/period-two/left-half-alone.md), [its condition for 0001](../Rule30Open/Columns/EtherDomain.md) and [the kit's C3](../findings/columns/left-half-c3.md), with its Lean checks for [0001](../Rule30Open/Columns/LeftHalf0001.md) and [0011 and 0111](../Rule30Open/Columns/LeftHalfDriven.md) | `python -m computations.held_map 22` | 5 s |
| [absorption.py](absorption.py) | [The absorption census](../findings/columns/absorption-census.md) and [the absorption route for period two](../negative-results/period-two/absorption-route.md) | `python -m computations.absorption census --cells 16 --steps 4000` | 17 s |
| [coupled.py](coupled.py) | [The white right half](../findings/period-two/white-right-half.md) | `python -m computations.coupled empty --depth 65536` | 1 s |
| [left_diagonals.py](left_diagonals.py) | [The white diagonals and period records](../findings/diagonals/left-records.md) | `python -m computations.left_diagonals 140000 100000` | 3 s |
| [frames.py](frames.py) | [The seed's past](../findings/frames/seed-past.md) and [the 2-adic trace](../findings/frames/two-adic-trace.md) | `python -m computations.frames 3000` | 16 s |
| [backgrounds.py](backgrounds.py) | [Periodic backgrounds](../findings/frames/periodic-backgrounds.md) and [the refuted conjecture](../negative-results/frames/periodic-column-preperiodic-row.md) | `python -m computations.backgrounds 9 2 2048` | 5 s |
| [sensitivity.py](sensitivity.py) | [The one-way valve](../findings/dynamics/one-way-valve.md) | `python -m computations.sensitivity 1024 8242` | 10 s |
| [algebra.py](algebra.py) | [The degree](../findings/structure/center-degree.md) and [the Duhamel form](../findings/structure/duhamel.md) | `python -m computations.algebra 9` | 1 s |
| [linear_complexity.py](linear_complexity.py) | [The linear complexity](../negative-results/complexity/linear-complexity.md) | `python -m computations.linear_complexity 65536` | seconds |
| [deformation.py](deformation.py) | [The deformation to Rule 150](../negative-results/structure/deformation-interpolation.md) | `python -m computations.deformation 16` | 1 s |

Several entries quote numbers whose code is not in this repository: the pruned search over seed extensions, the
period-two searches past support 24, the learned models, the automaton bounds, the coarse-graining closures and the
invariant searches. Each such entry says so. A port to `computations/`, with a test, is a welcome contribution.
