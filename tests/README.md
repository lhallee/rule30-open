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
  `extra_tables`, `census_tables`, `gap_entries`, `reach_nodes`, `game.kit_blocks`, `game.game_ranks`,
  `game.game_moves`, `coin_lock.certificate`, `defect_potential.closed_strips`, `absorption.family_terms`,
  `locks.back_table` and `sheaf_sections.linear_limit` keep their results for the arguments asked again, as read-only
  arrays, and the certificates of the coin finding and the long center column are module-scoped fixtures. No test
  calls `lock_chain.block_traps` (about 570 s for its 1,648 traps) or builds every trap.
- **Reverse search and vectorized stepping.** `locks.back_closure` runs a breadth-first search on the reversed graph
  (`locks.reverse_graph`), `locks.back_search` sorts a small frontier instead of scanning the game, and
  `locks.predecessors` reads 11 cells at a time from a table. `game.game_graph` takes its moves from
  `game.game_moves`, `lock_word.unreachable` and `gate_census.gap_states` are backward searches, and
  `game.necklaces` marks necklaces with integer rotations. `coin_lock` iterates on the windows outside the
  certificate only, `absorption.family_depth` tests every alignment at once, `tail_census.ring_backgrounds` steps each
  ring state once (`orbit_entry`), `space_time_periodic.cycles` stops squaring once the image stops shrinking, and
  `right_half.column_one` and `slip_geometry.column_one` cut the row to the light cone. Their results are unchanged,
  and the tests that check them against forward searches, direct runs with `step` and the quoted counts still pass.
- **Tests that run many rows at once.** The brute-force checks in the tests (`test_ring_orbits`, `test_ten_coin`,
  `test_natural_coin`, the direct runs of `test_ether_descent.py`) step every state together as numpy arrays or
  integer rows and stop at the first difference, and `direct_runs` is itself checked against `ether_certificate.step`.
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
| Scans of 10,000 and 20,000 steps in `halves_apart` for the split walls (three halves of 000000101101 in its second trap) | `--halves-apart` |
| The survey of the game at periods 9 and 10 | `python -m computations.game --max-period 10 --workers 2` |
| Rings of 12 to 16 cells, backgrounds of period 12 and `witnesses(12)` | `python -m computations.space_time_periodic --witnesses`, `--table` |
| The walls the backgrounds seed at 16 cells | `python -m computations.space_time_periodic 8,9,10,11,12,13 --walls 16` |
| Width 16 expected entry times and decay factor of the coin finding | `python -m computations.coin_lock 0001 0011 0111 --widths 14 16 18` |
| The census at 12 cells (latest entries 544, 980, 416) | `python -m computations.absorption census --cells 12 --steps 1200` |
| Entry of half 2 into `t001` at step 35,536 | `python -m computations.period_three --trap --cells 10 --steps 400000` |
| Row counts of A New Kind of Science at periods 9 and 10 | `python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10 --counts` |
| The second Lean block of `BitPhases` | `python -m computations.bit_game --phases 17,18`; the kernel checks every block |

## Measured

`python -m pytest -q --durations=0` collected 405 tests: 404 passed and 1 was skipped (`test_late_onset.py` needs
`pysat`, which this environment lacks), in 58.6 s and 59.7 s (`time`: 60.8 s real) serially on 2026-11-01. The
machine was not idle: a Lean build ran on one of its four cores (load average 1.2 to 1.4), and the suite runs on one
core, so the idle time is about the same. The per-test durations of the run sum to 56.8 s; collection and imports take
the other 2 s. The target of 50 s is not met.

The slowest tests in the full run, in seconds: `test_period_rate` 1.8, `test_lock_word` 1.3,
`test_universal_word` 1.3, `test_mixed_nodes` 1.3, `test_census_traps` 1.2, `test_coin_chain` 1.2,
`test_trap_pairs` 1.2, `test_lock_avoid_growth` 1.0, `test_natural_traps` 0.9, `test_trap_sets` 0.9,
`test_reach_wide_carried` 0.9, `test_second_nine_wall` 0.9, `test_bit_blocks` 0.9, `test_space_time_periodic` 0.8,
`test_apart_traps` 0.8, `test_game_masks` 0.8. Run alone, without the results the earlier tests leave in the caches,
`test_census_traps` takes 1.9 s, `test_trap_pairs` 1.5 s and `test_natural_traps` 1.4 s. About 25 further tests take
0.5 to 0.8 s each. `test_class_blocks_wide.py::test_certificate_checks` takes 0.7 s.

What is left is the work the checks need, not repeated work. `test_period_rate` runs power iterations of 500 periods
and to the tolerance 1e-10 because its assertions compare rates to 1e-6 and 1e-9; `test_lock_word` and
`test_universal_word` run each universal word over every window of the game, which is the claim; `test_mixed_nodes`,
`test_census_traps` and `test_trap_pairs` build games of 16 cells and their reverse searches once each. What does not
help: `gap_entries` vectorized over all halves with `absorption.step_rows` gives the same entries but runs three times
slower than the loop over integers; `coin_lock.entry_paths` over the windows outside the certificate only runs slower
than over every window; and `np.take` in place of indexing in the run of a lock word saves under 0.1 s. Getting under
50 s would take smaller samples in the tests of 0.5 s and more, or running the suite on worker processes with
pytest-xdist, which this file's rule of no worker processes excludes.

The tests of other collaborators in this folder count toward the limit like the others; outside `test_computations.py`
the files together take about 16 s, and no test there takes over 0.7 s.
