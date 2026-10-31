# Tests

`python -m pytest` runs on your machine, on a CPU, not in continuous integration. The limit for the whole suite is
one minute. Each computation in `computations/` keeps a test against an independent check (a second implementation, a
known sequence, or a number its entry quotes), on small cases; the large runs belong to the reproduce commands of the
entries.

## Open work: the suite takes about 20 minutes

Measured with `python -m pytest --durations=0`, in four shards on four cores; the tests not listed take under 3 s each.

| Test | Seconds |
|---|---:|
| `test_wide_walls` | 239 |
| `test_trap_sets` | 227 |
| `test_period_rate` | 169 |
| `test_own_locks` | 127 |
| `test_unreached` | 76 |
| `test_coverage` | 39 |
| `test_chain_family_01111` | 38 |
| `test_mixed_nodes` | 27 |
| `test_wall_natural` | 24 |
| `test_space_time_periodic` | 23 |
| `test_wide_window` | 21 |
| `test_scan_six` | 20 |
| `test_trap_pairs` | 17 |
| `test_missed_traps` | 17 |
| `test_ten_traps` | 16 |
| `test_eleven_twelve_traps` | 13 |
| `test_fifteen_walls` | 13 |
| `test_far_walls` | 12 |
| `test_white_lock` | 12 |
| `test_coin_chain` | 11 |
| `test_nine_white` | 10 |
| `test_six_refuted` | 7 |

One shard did not finish: `test_census_traps` alone ran more than ten minutes, and `test_apart_traps`,
`test_back_tables`, `test_refuted_traps`, `test_reach_wide_carried` and `test_natural_traps` were not timed.

Most of the time goes to rebuilding whole data sets: every trap of a module (`module_entries`, `block_traps`,
`coverage.trap_blocks`), whole Lean modules regenerated to compare with the files, games of 20 or 22 cells, and long
iterations.

To fix it:

1. Delete the tests that only repeat a check made elsewhere. The kernel checks every trap table (`WTrap.check`), so a
   test need not rebuild every trap and compare it with its Lean file: one small entry per generator tests the
   generator.
2. Shrink the rest to small cases that run the same functions against the same independent check: games of at most
   16 cells, one or two blocks per module, short runs.
3. Share any expensive object across tests with a module-scoped fixture, and never build every trap of the modules.
4. Check with `python -m pytest --durations=20` that the whole suite takes under a minute.
