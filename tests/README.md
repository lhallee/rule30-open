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
  generator is exercised, the file is not regenerated. The gap modules work the same way: `lean_ten_gap` and
  `lean_gap` take a tuple of phases, the test generates one phase and reads every entry of the other phases from the
  Lean file, and `test_bit_blocks` builds the last block of each module.
- **Small games.** Games of at most 16 cells, one or two blocks per module, short runs. The claims at 20 and 22 cells
  have a small analog that runs the same function (the natural trap of 0001111110011 at 17 cells for the walls and the
  unreached nodes) and are left to the entries' reproduce commands.
- **One BLAS thread.** `tests/conftest.py` sets `OPENBLAS_NUM_THREADS`, `OMP_NUM_THREADS` and `MKL_NUM_THREADS` to 1
  before numpy loads. The eigenvalues of a matrix of 700 rows took 8 s with four BLAS threads on a machine with one
  busy core and take 0.45 s with one; the results are those of the same LAPACK routines.
- **Shared objects.** `coverage.module_blocks`, `coverage.trap_blocks`, `lock_chain.tables`, `carried`,
  `carried_word`, `extra_tables`, `census_tables`, `gap_entries`, `reach_nodes`, `game.kit_blocks`,
  `game.game_ranks`, `game.game_moves`, `coin_lock.certificate`, `defect_potential.closed_strips`,
  `absorption.family_terms`, `locks.back_table` and `sheaf_sections.linear_limit` keep their results for the arguments
  asked again, as read-only arrays, and the certificates of the coin finding are module-scoped fixtures. Two session
  fixtures in `conftest.py` serve several files: `center_rows`, the first 65,536 digits of the center column and the
  rows at 16,384, 32,768 and 49,152 steps, stepped one row at a time (for `test_long_window`, `test_wide_window` and
  the long window of `test_lean_statements.py`), and `deep_diagonals`, the stream of `settled_slope` to depth 10,000
  over 15,600 steps (for `test_settled_slope.py`, `test_front_walker.py`, `test_onset_heuristics.py` and `test_settled_words.py`). No test calls `lock_chain.block_traps` (about 570 s
  for its 1,648 traps) or builds every trap.
- **Reverse search and vectorized stepping.** `locks.back_closure` runs a breadth-first search on the reversed graph
  (`locks.reverse_graph`), `locks.back_search` sorts a small frontier instead of scanning the game, and
  `locks.predecessors` reads 11 cells at a time from a table. `locks.locked_search` skips the second search of a
  phase when the first adds no node and stops once every node is mixed; `locks.locked_nodes` leaves out the search for
  the nodes that reach a locked one when the caller needs only the locked ones. `bit_game.phase_rounds` closes each
  round with `back_closure`, `coin_lock.entry_paths` relaxes only the windows whose successor changed after a first
  full sweep (the same distances and first values, in the same order of updates), `lock_chain.carried_block` reads a
  carried block from the chain without building its trap, and `lock_chain.least_period` finds the first return of the
  word in its square. `rule30.distinct` (sort and compare neighbors) takes the place of `np.unique`, whose hash path is
  ten times slower on these arrays in numpy 2.5. `game.game_graph` takes its moves from `game.game_moves`,
  `lock_word.unreachable` and `gate_census.gap_states` are backward searches, and `game.necklaces` marks necklaces
  with integer rotations. `coin_lock` iterates on the windows outside the certificate only, `absorption.family_depth`
  tests every alignment at once, `tail_census.ring_backgrounds` steps each ring state once (`orbit_entry`),
  `space_time_periodic.cycles` stops squaring once the image stops shrinking, and `right_half.column_one` and
  `slip_geometry.column_one` cut the row to the light cone. Their results are unchanged, and the tests that check them
  against forward searches, direct runs with `step` and the quoted counts still pass;
  `test_entry_paths_against_full_sweeps` checks `entry_paths` against the sweep over every window and `distinct`
  against `np.unique`, and `test_carried_blocks` checks `carried_block` against the block of `carried`.
- **Compiled once.** `seed_onsets` keeps its compiled C searches in a folder of the temporary directory that only the
  user can write, under a hash of the source, the compiler, the flags and the machine, so a later run reuses them;
  `class_certificate.step` keeps the moves that `check` asks twice.
- **Tests that run many rows at once.** The brute-force checks in the tests (`test_ring_orbits`, `test_ten_coin`,
  `test_natural_coin`, `test_cut_entries`, the direct runs of `test_ether_descent.py` and `test_run_mechanism.py`, and
  `driven_rows_many` for `test_core_persists_after_entry`) step every state together as numpy arrays or integer rows,
  cut to the light cone, and stop at the first difference; `driven_rows_many` is itself checked against
  `right_half.driven_row` in `test_driven_spacetime`. The plain recursions of `test_gap_traps.py` and
  `test_three_runs.py` step each state's moves cell by cell once and reuse them.
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
| Every phase of TenGap and WallGaps generated and compared with its Lean file | `--lean-ten-gap`, `--lean-wall-gaps` |
| The large natural trap of 61,857 states | `--lean-large` |
| The second nine wall with the cap of 100,000 states | `--natural 2,3,5,6,7,9 --steps 20000` |
| Universal words of 0001 and 0011 at width 16 | `python -m computations.coin_lock 0001 0011 0111 --widths 14 16 18` |
| Backgrounds of period 11 and the walls of period 10 at 13 cells | `python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10,11,12,13,14 --table`, `python -m computations.space_time_periodic 10 --walls 13` |
| The held map tree of 0001 to support 80 | `python -m computations.held_map 80 --word 0001 --tree check` |
| Slow halves of 0001 and 0011 at 12 cells | `python -m computations.slow_halves 0001 0011 0111 --beam 512 --start 12 --stop 64 --steps 8000` |
| All three certificates of PeriodFourCertificate as Lean text | `python -m computations.lock_certificate --lean` |
| The lock census of period 6 modulo 12 at 13 cells | `python -m computations.locks --periods 6 --census 13 --repeat 2 --wide` |

## Measured

`python -m pytest -q --durations=40 -p no:cacheprovider` collects 533 tests: 532 pass and 1 is skipped
(`test_late_onset.py` needs `pysat`, which this environment lacks). Serially on one core of a machine with four, with no
other job running, the suite takes 44 to 49 s of wall time; the per-test durations (setup and call) sum to 42 to 46 s,
and collection and imports take the other 2 to 3 s, of which importing `ripser` and `sklearn` for `test_persistence.py`
is about 0.9 s. The spread between runs is the machine's, which runs one fixed computation in anywhere from 0.47 to
1.1 s.

The slowest tests, in seconds (the least over the runs): `test_long_window` 1.0 (0.4 of it the shared fixture
`center_rows`), `test_period_rate` 0.8, `test_trap_pairs` 0.8, `test_lock_avoid_growth` 0.7, `test_mixed_nodes` 0.7,
`test_census_traps` 0.7, `test_game_survey` 0.7, `test_reach_wide_carried` 0.5, `test_cut_entries` 0.5,
`test_class_blocks_wide.py::test_certificate_checks` 0.5, `test_lock_word` 0.5 and `test_unreached` 0.5. About 25
further tests take 0.3 to 0.5 s each, and 361 take under 0.1 s, 7.4 s together.

What is left is the work the checks need, not repeated work. `test_period_rate` and `test_lock_avoid_growth` run
`coin_lock.power_bound` to the tolerance 1e-12 because their assertions compare rates to six digits;
`test_long_window` runs `long_window.simulate` over the 65,536 steps that `LongWindow` states; `test_trap_pairs`,
`test_mixed_nodes` and `test_census_traps` build games of 16 cells and their locked nodes, one breadth-first search of
about 30 ms per value and white phase; `test_game_survey` starts two worker processes, which is what it tests. What
does not help: `gap_entries` vectorized over all halves with `absorption.step_rows` gives the same entries but runs
three times slower than the loop over integers; reusing buffers or a sparse matrix product in `power_bound`, and other
thresholds for Python's garbage collector, save nothing measurable; `np.take` in place of indexing in the run of a
lock word saves under 0.1 s; and skipping the second search of `locks.mixed_nodes` when the first adds nothing, as
`locked_search` does, saves nothing, because `back_search` from a seed of one phase is cheap. Getting under 45 s would
take smaller samples in the tests of 0.4 s and more, or running the suite on worker processes with pytest-xdist, which
this file's rule of no worker processes excludes.

The tests of other collaborators in this folder count toward the limit like the others; outside `test_computations.py`
the files together take about 17 s, and no test there takes over 0.6 s.
