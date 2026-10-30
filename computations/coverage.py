"""How much of each period the exclusions and the reductions in Lean reach.

For each period: the primitive blocks; those excluded outright, by the finite game at width 6, 10 or 14 or by the kit
(`game.first_width`, `game.kit_blocks`), each of which is excluded in Lean up to period 20; those that a trap in Lean
reduces to entry (the blocks of `WordTraps`, `NineTraps`, `TenTraps`, `ElevenTraps`, `TwelveTraps` and
`PeriodFourCertificate`, and the kit's `t001` for 001); those that a steering sequence of the `LockBlocks` modules
reduces to a condition on column 14; and the rest, which no method here reaches.

    python -m computations.coverage --max-period 12   # about 10 minutes
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tqdm.auto import tqdm

from computations import game, lock_chain

ROOT = Path(__file__).resolve().parent.parent


def trap_blocks() -> dict[str, str]:
    """The blocks that a trap in Lean reduces to entry, each as its least rotation, with the module that holds it."""
    found: dict[str, str] = {"001": "the kit's t001"}
    for name, *_ in lock_chain.TRAPS:
        found.setdefault(lock_chain.tables(name)["word"], "WordTraps")
    found.setdefault(lock_chain.tables("trap001011111")["word"], "WordTraps")
    for distance in lock_chain.nine_distances():
        found.setdefault(lock_chain.carried("trap001011111", distance)["word"], "NineTraps")
    found.setdefault(lock_chain.tables("trap001010011")["word"], "NineTraps")
    for distance in lock_chain.ten_distances():
        found.setdefault(lock_chain.carried("trap0000010001", distance)["word"], "TenTraps")
    for period, module in ((11, "ElevenTraps"), (12, "TwelveTraps")):
        for _, _, word in lock_chain.wall_distances(period, 40):
            found.setdefault(word, module)
    for word in ("0001", "0011", "0111"):
        found.setdefault(word, "PeriodFourCertificate")
    return found


def steered_blocks() -> set[str]:
    """The blocks of the entries `Steered` of the LockBlocks modules, read from their Lean sources."""
    found = set()
    for path in sorted((ROOT / "Rule30Open" / "Columns").glob("LockBlocks*.lean")):
        found |= set(re.findall(r"def steer_([01]+) : Steered", path.read_text(encoding="utf-8")))
    return found


def coverage(max_period: int) -> list[tuple[int, int, int, int, int, int]]:
    """For each period up to `max_period`: the number of primitive blocks, those excluded outright, those reduced to
    entry into a trap (and not excluded), those reduced by steering only, and the rest."""
    traps, steered = trap_blocks(), steered_blocks()
    kit = game.kit_blocks(max_period)
    rows = []
    for period in range(1, max_period + 1):
        blocks = game.necklaces(period)
        excluded = {block for block in tqdm(blocks, desc=f"period {period}", file=sys.stderr, mininterval=5)
                    if block in kit or game.first_width(block, [6, 10, 14]) is not None}
        trapped = {block for block in blocks if block in traps} - excluded
        steering = {block for block in blocks if block in steered} - excluded - trapped
        rest = len(blocks) - len(excluded) - len(trapped) - len(steering)
        rows.append((period, len(blocks), len(excluded), len(trapped), len(steering), rest))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-period", type=int, default=12)
    args = parser.parse_args()
    print("| Period | Blocks | Excluded | Reduced to entry into a trap | Reduced by steering only | Not reached |")
    print("|---:|---:|---:|---:|---:|---:|")
    for period, total, excluded, trapped, steering, rest in coverage(args.max_period):
        print(f"| {period} | {total} | {excluded} | {trapped} | {steering} | {rest} |", flush=True)


if __name__ == "__main__":
    main()
