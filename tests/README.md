# Tests

`python -m pytest` runs on your machine, on a CPU, not in continuous integration. The limit for the whole suite is
one minute, serially, with no worker processes. Each computation in `computations/` keeps a test against an
independent check (a second implementation, a known sequence, a direct run with `step`, or a number its entry quotes),
on small cases; the large runs belong to the reproduce commands of the entries.

## How the suite stays fast

- **One entry stands for a module.** The Lean kernel checks every trap table (`WTrap.check`), so a test need not
  rebuild every trap of a module and compare it with its Lean file. A test builds a sample of the entries of a module
  (every fifth, every tenth, the first), checks each with `is_lock`, `trap_reach`, `apart_closed` and a direct run with
  `step`, and then restricts the generator (`lean_extra`, `lean_pairs`, `lean_apart_traps`, ...) to one entry by
  patching its list of entries with `monkeypatch` and checks that the text it writes is text of the module's file. The
  generator is exercised, the file is not regenerated.
- **Small games.** Games of at most 16 cells, one or two blocks per module, short runs. The claims at 20 and 22 cells
  have a small analog that runs the same function (the natural trap of 0001111110011 at 17 cells for the walls and the
  unreached nodes) and are left to the entries' reproduce commands.
- **Shared objects.** `coverage.module_blocks`, `coverage.trap_blocks`, `lock_chain.tables`, `carried`,
  `extra_tables`, `census_tables`, `gap_entries` and `game.kit_blocks` keep their results for the arguments asked
  again, and the certificates of the coin finding are module-scoped fixtures. No test calls `lock_chain.block_traps`
  (about 570 s for its 1,648 traps) or builds every trap.
- **Reverse search and vectorized stepping.** `locks.back_closure` runs a breadth-first search on the reversed graph
  (`locks.reverse_graph`), `game.game_graph` takes its moves from `game.moves`, `lock_word.unreachable` is a backward
  search, and `game.necklaces` marks necklaces with integer rotations. Their results are unchanged, and the tests that
  check them against forward searches and the old counts still pass.
- **No plugins that the suite does not use.** `pyproject.toml` switches off pytest plugins of the global environment
  (`addopts`), which took about 20 s to load.

A test is never skipped, expected to fail or deselected to meet the limit.

## What the reproduce commands cover

These checks ran inside the earlier tests at their full size and now run only by the command of the entry that owns
them (the command is in `computations/README.md`):

| Dropped from the suite | Command that keeps it (`python -m computations.lock_chain ...` unless noted) |
|---|---|
| Every trap of a module compared with its Lean file | `--lean-census`, `--lean-census-large`, `--lean-long-large`, `--lean-extra`, `--lean-long`, `--lean-large`, `--lean-missed`, `--lean-pairs`, `--lean-wall-natural`, `--lean-fifteen`, `--lean-trap-sets`, `--lean-apart-traps`, `--lean-wide-walls`, `--lean-wide-census` |
| Games of 20 and 22 cells, wide reach of the carried traps | `--wide-reach`, `--wide-reach-carried` |
| Own locks of 20 and 22 cells, the census of apart traps | `--own-census`, `--census-apart`, `--apart-census` |
| The search over cell counts 16 to 64 of the white half under 001 | `--white` |
| Chain families with the full scan of seeds | `--short`, `--chain-family` |
| Scans of 20,000 steps in `halves_apart` for the split walls | `--halves-apart` |
| The survey of the game at period 10 | `python -m computations.game --max-period 10 --workers 2` |
| Rings of 12 to 16 cells, backgrounds of period 12 and `witnesses(12)` | `python -m computations.space_time_periodic --witnesses`, `--table`, `--walls` |
| Width 16 expected entry times and decay factor of the coin finding | `python -m computations.coin_lock 0001 0011 0111 --widths 14 16 18` |
| The census at 12 cells (latest entries 544, 980, 416) | `python -m computations.absorption census --cells 12 --steps 1200` |
| Entry of half 2 into `t001` at step 35,536 | `python -m computations.period_three --trap --cells 10 --steps 400000` |
| Row counts of A New Kind of Science at periods 9 and 10 | `python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10 --counts` |
| The second Lean block of `BitPhases` | `python -m computations.bit_game --phases 17,18`; the kernel checks every block |

## Measured

`python -m pytest -q` ran 210 tests, all passing, in 69.4 s serially on 2026-10-31. The limit is 60 s, so the suite
is about 9 s over. Before this pass the same suite took
80 minutes (4,768 s, 143 tests, 8 failing for the missing kit and one encoding error).

The slowest tests, in seconds: `test_period_rate` 3.0, `test_wall_natural` 2.9, `test_space_time_periodic` 1.6,
`test_mixed_nodes` 1.7, `test_long_window` 1.7, `test_reach_wide_carried` 1.6, `test_game_survey` 1.5,
`test_trap_sets` 1.5, `test_forcing` 1.4. About 70 further tests take 0.3 to 1.5 s each, which is where the remaining
time is. What does not help: `period_rate` in `test_period_rate` runs 1,876 and 2,995 steps for its two settled rates
because its tolerance sets them, and the assertions need that tolerance; the scan of `halves_apart` in
`test_wall_natural` gives a different split below 10,000 steps (21 halves at 3,000 steps, three in a trap of 24,128
states at 5,000); `gap_entries` vectorized over all halves with `absorption.step_rows` gives the same entries but
runs three times slower than the loop over integers; and `coin_step` vectorized over the phases runs slower too. Two
ways to get under a minute remain: smaller samples in the tests of 0.3 s and more, about a third of their time, or
running the suite on four worker processes with pytest-xdist, which this file's rule of no worker processes excludes.

The tests of other collaborators in this folder (`test_background_halves.py`, `test_held_shift.py`,
`test_crossing_bounds.py`, `test_obdd_orders.py`, `test_space_window.py`, `test_alternating_horizon.py`,
`test_diagonal_cones.py`, `test_limit_windows.py`) count toward the limit like the others; together they take about
3 s, and none takes over 2 s.
