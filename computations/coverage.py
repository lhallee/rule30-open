"""How much of each period the exclusions and the reductions in Lean reach.

For each period: the primitive blocks; those excluded outright, by the finite game at width 6, 10 or 14 or by the kit
(`game.first_width`, `game.kit_blocks`), each of which is excluded in Lean up to period 20; those that a trap in Lean
reduces to entry (the blocks of `WordTraps`, `NineTraps`, `TenTraps`, `ElevenTraps`, `TwelveTraps`, `ThirteenTraps`,
`FourteenTraps`, `NaturalTraps`, `NaturalTrapsLarge`, `NaturalTrapsLong`, `NaturalTrapsLongLarge`, `FarWalls`,
`CensusTraps13`, `CensusTraps14`, `CensusTraps15`, `CensusTrapsLarge`, `CensusTrapsLarge15`, `FifteenWalls`,
`TrapPairs`, `NaturalTrapsWalls`, `TrapSets`, `ApartTraps`, `WideWalls` and `PeriodFourCertificate`, and the four traps
for 001 of `Traps001`), counting only traps that pass the test of reach at 20 and 22 cells (`lock_chain.UNREACHED`,
`lock_chain.UNREACHED_WIDE`), that no half of the natural scan stays apart from (`lock_chain.APART`) and that no other
trap of their block is apart from (`lock_chain.APART_TRAPS`); those that a steering sequence of the `LockBlocks`
modules reduces to a condition on column 14; and the rest, which no method here reaches.

    python -m computations.coverage --max-period 15   # about ten minutes
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tqdm.auto import tqdm

from computations import game, lock_chain

ROOT = Path(__file__).resolve().parent.parent


def module_blocks() -> list[tuple[str, str]]:
    """Every block that a trap in Lean reduces to entry, each as its least rotation, with the module that holds the
    trap, once per trap, in the order of the modules."""
    found: list[tuple[str, str]] = [("001", "Traps001")]
    found += [(lock_chain.tables(name)["word"], "WordTraps") for name, *_ in lock_chain.TRAPS]
    found.append((lock_chain.tables("trap001011111")["word"], "WordTraps"))
    found += [(lock_chain.carried("trap001011111", distance)["word"], "NineTraps")
              for distance in lock_chain.nine_distances()]
    found.append((lock_chain.tables("trap001010011")["word"], "NineTraps"))
    found += [(lock_chain.carried("trap0000010001", distance)["word"], "TenTraps")
              for distance in lock_chain.ten_distances()]
    for period, module in ((11, "ElevenTraps"), (12, "TwelveTraps"), (13, "ThirteenTraps"), (14, "FourteenTraps")):
        found += [(word, module) for _, _, word in lock_chain.wall_distances(period, lock_chain.WALL_DEPTHS[period])]
    for module, entries in (("NaturalTraps", lock_chain.EXTRA_TRAPS), ("NaturalTrapsLarge", lock_chain.LARGE_TRAPS),
                            ("NaturalTrapsLong", lock_chain.LONG_TRAPS),
                            ("NaturalTrapsLongLarge", lock_chain.LONG_LARGE)):
        found += [(word, module) for word, *_ in entries]
    found += [(lock_chain.carried(name, distance)["word"], "FarWalls")
              for entries in lock_chain.FAR_WALLS.values() for name, distance in entries]
    for period, entries in lock_chain.CENSUS_TRAPS.items():
        found += [(block, f"CensusTraps{period}") for block, *_ in entries]
    found += [(block, "CensusTrapsLarge") for block, *_ in lock_chain.CENSUS_LARGE]
    found += [(block, "CensusTrapsLarge15") for block, *_ in lock_chain.CENSUS_LARGE15]
    found += [(lock_chain.fifteen_tables(wall, distance)["word"], "FifteenWalls")
              for wall, distance in lock_chain.FIFTEEN_DISTANCES]
    carried = {(module, name): build for module, name, build in lock_chain.module_entries()}
    found += [(carried[key]()["word"], "WideWalls") for key in lock_chain.WIDE_WALLS]
    found += [(block, "TrapPairs") for block in lock_chain.PAIRS]
    found += [(word, "NaturalTrapsWalls") for word, *_ in lock_chain.WALL_NATURAL + lock_chain.WALL_SPLIT]
    found += [(block, "TrapSets") for block, *_ in lock_chain.TRAP_SETS]
    found += [(block, "ApartTraps") for block, *_ in lock_chain.APART_TRAPS]
    found += [(word, "PeriodFourCertificate") for word in ("0001", "0011", "0111")]
    return found


def trap_blocks() -> dict[str, str]:
    """The blocks that a trap in Lean reduces to entry, each as its least rotation, with the first module that holds
    one."""
    found: dict[str, str] = {}
    for block, module in module_blocks():
        found.setdefault(block, module)
    return found


def refuted_blocks() -> set[str]:
    """The blocks of `trap_blocks` whose every trap is refuted: it fails the test of reach (`lock_chain.UNREACHED`),
    so some node of the finite game of `lock_chain.REACH_WIDTH` cells cannot reach it, or a half of the block's
    natural scan is inside a closed set apart from it (`lock_chain.APART`), or it fails the test of reach in the game
    of 22 cells (`lock_chain.UNREACHED_WIDE`), or another trap of its block is apart from it (`lock_chain.APART_TRAPS`);
    either way entry into it is false and its reduction empty. The pairs of `ApartTraps` and `WideWalls` hold the blocks
    of some of these traps again, with a trap apart from the refuted one. The kit's `t001` and its ether-and-wall
    family, behind `PeriodFourCertificate`, pass the test of reach ([reach of the kit's
    conjectures](../findings/columns/kit-absorption-reach.md))."""
    refuted = (lock_chain.UNREACHED, lock_chain.APART, lock_chain.UNREACHED_WIDE, lock_chain.apart_refuted())
    passing = {block for block, module in module_blocks()
               if not any(block in found.get(module, ()) for found in refuted)}
    return set(trap_blocks()) - passing


def steered_blocks() -> set[str]:
    """The blocks of the entries `Steered` of the LockBlocks modules, read from their Lean sources."""
    found = set()
    for path in sorted((ROOT / "Rule30Open" / "Columns").glob("LockBlocks*.lean")):
        found |= set(re.findall(r"def steer_([01]+) : Steered", path.read_text(encoding="utf-8")))
    return found


def coverage(max_period: int) -> list[tuple[int, int, int, int, int, int, int]]:
    """For each period up to `max_period`: the number of primitive blocks, those excluded outright, those reduced to
    entry into a trap that passes the test of reach (and not excluded), those reduced by steering only, those whose
    every trap fails the test, and the rest."""
    traps, refuted, steered = trap_blocks(), refuted_blocks(), steered_blocks()
    kit = game.kit_blocks(max_period)
    rows = []
    for period in range(1, max_period + 1):
        blocks = game.necklaces(period)
        excluded = {block for block in tqdm(blocks, desc=f"period {period}", file=sys.stderr, mininterval=5)
                    if block in kit or game.first_width(block, [6, 10, 14]) is not None}
        trapped = {block for block in blocks if block in traps and block not in refuted} - excluded
        steering = {block for block in blocks if block in steered} - excluded - trapped
        empty = {block for block in blocks if block in refuted} - excluded - steering
        rest = len(blocks) - len(excluded) - len(trapped) - len(steering) - len(empty)
        rows.append((period, len(blocks), len(excluded), len(trapped), len(steering), len(empty), rest))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-period", type=int, default=12)
    args = parser.parse_args()
    print("| Period | Blocks | Excluded | Reduced to entry into a trap | Reduced by steering only | Only refuted traps "
          "| Not reached |")
    print("|---:|---:|---:|---:|---:|---:|---:|")
    for period, total, excluded, trapped, steering, empty, rest in coverage(args.max_period):
        print(f"| {period} | {total} | {excluded} | {trapped} | {steering} | {empty} | {rest} |", flush=True)


if __name__ == "__main__":
    main()
