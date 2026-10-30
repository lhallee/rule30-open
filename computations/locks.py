"""Locks of the finite game that every window can be steered into, block by block.

Let column k repeat a block b of period P; a node of the finite game of `game.py` is a phase and the cells
k + 1 .. k + width, and each step takes a value of the free cell, column k + width + 1. Call a node locked when along
every continuation, whatever the free cell does, the column left of k (`column` of `game.game_graph`) takes one value at
each phase. A row whose node is ever locked has that column eventually periodic, which Jen's theorem on adjacent columns
forbids. The game excludes b when every play is eventually locked; here the question is weaker and of a different kind:
whether from every node some values of the free cell lead to a locked node. If they do, one sequence of values leads
every node there (`lock_word.universal_word` builds such sequences for the kit's family), so a column that repeats b
keeps the column beyond the window off that sequence forever, as `Rule30Open.Columns.LockWord` proves for the three
words of period four.

`lock_info` computes the locked nodes as the complement of the nodes that can reach both values at one phase, and
whether every node can reach them. `survey` runs it on every primitive block of the given periods.

    python -m computations.locks --periods 4,8,10,11,12 --width 13 --workers 3   # about 3 min
    python -m computations.locks --profile --workers 3   # adds about 2 min
    python -m computations.locks --lean --workers 3   # the entries of LockBlocks11 and LockBlocks12
"""

from __future__ import annotations

import argparse
import functools
import itertools
import multiprocessing
import sys

import numpy as np
from tqdm.auto import tqdm

from computations import game


def back_closure(seed: np.ndarray, source: np.ndarray, target: np.ndarray) -> np.ndarray:
    """The nodes from which some walk along the moves reaches the seed."""
    # seed: (n,); source, target: (m,)
    reached = seed.copy()  # (n,)
    frontier = seed.copy()  # (n,)
    while frontier.any():
        before = np.zeros(seed.size, dtype=bool)  # (n,)
        before[source[frontier[target]]] = True
        frontier = before & ~reached
        reached |= frontier
    return reached  # (n,)


def lock_info(block: str, width: int) -> tuple[np.ndarray, np.ndarray]:
    """The locked nodes, and the nodes from which some values of the free cell reach a locked node."""
    source, target, _, _, column = game.game_graph(block, width)  # (2 p n,), (2 p n,), _, _, (p n,)
    phase = np.arange(column.size) >> width  # (p n,)
    mixed = np.zeros(column.size, dtype=bool)  # (p n,), nodes that can reach both values at one phase
    for ph in range(len(block)):
        here = phase == ph  # (p n,)
        mixed |= back_closure(here & column, source, target) & back_closure(here & ~column, source, target)
    locked = ~mixed  # (p n,)
    return locked, back_closure(locked, source, target)  # (p n,), (p n,)


def steerable(block: str, width: int) -> bool:
    """Whether some node is locked and every node can be steered into a locked node."""
    locked, reach = lock_info(block, width)  # (p n,), (p n,)
    return bool(locked.any() and reach.all())


def survey(periods: list[int], width: int, workers: int = 1) -> dict[int, list[str]]:
    """For each period, the primitive blocks whose game at this width has locks that every node can be steered into."""
    found = {}
    for period in periods:
        blocks = game.necklaces(period)
        task = functools.partial(steerable, width=width)
        progress = functools.partial(tqdm, total=len(blocks), desc=f"period {period}", file=sys.stderr, mininterval=5)
        if workers > 1:
            with multiprocessing.get_context("spawn").Pool(workers) as pool:
                flags = list(progress(pool.imap(task, blocks, chunksize=2)))
        else:
            flags = [task(block) for block in progress(blocks)]
        found[period] = [block for block, flag in zip(blocks, flags) if flag]
    return found


def steering(block: str, width: int) -> tuple[list[int], dict[int, list[int]]]:
    """A sequence of values of the free cell that brings every node, started at any phase, to a locked node
    (`lock_word.universal_word` with the locked nodes as target), and the windows where it leaves them, by final phase."""
    from computations.lock_certificate import successor_table
    from computations.lock_word import universal_word
    period = len(block)
    locked, _ = lock_info(block, width)  # (p n,)
    values = universal_word(block, locked.reshape(period, 1 << width))
    successors = successor_table(block, width)  # (p, 2, 2^W)
    finals: dict[int, set[int]] = {}
    for start in range(period):
        windows = np.arange(1 << width, dtype=np.int64)  # (2^W,)
        for step, value in enumerate(values):
            windows = successors[(start + step) % period, value][windows]  # (2^W,)
        finals.setdefault((start + len(values)) % period, set()).update(np.unique(windows).tolist())
    return values, {phase: sorted(states) for phase, states in sorted(finals.items())}


def lean_entry(block: str) -> str:
    """The Lean entry `LockBlocks.Steered` for one block at width 13, the width `Steered.check` uses: the block, the
    sequence as a number, value i at bit i, its length and the final windows by phase, with the theorem that the check
    passes."""
    values, finals = steering(block, 13)
    word = sum(v << i for i, v in enumerate(values))
    groups = ", ".join(f"({phase}, [{', '.join(map(str, states))}])" for phase, states in finals.items())
    lines = [f"  {len(values)}, "]
    for k, item in enumerate(f"[{groups}]⟩".split(", ")):
        piece = item if k == 0 else ", " + item
        if len(lines[-1]) + len(piece) > 119:
            lines[-1] += ","
            lines.append("    " + item)
        else:
            lines[-1] += piece
    return (f"def steer_{block} : Steered := ⟨{len(block)}, 0b{block},\n"
            f"  0x{word:x},\n" + "\n".join(lines) + "\n\n"
            f"set_option maxHeartbeats 0 in\n"
            f"theorem steer_{block}_check : steer_{block}.check = true := by decide +kernel\n")


def profile(block: str, width: int) -> tuple[float, int, float]:
    """The fraction of nodes that are locked, the length of the steering sequence of `steering`, and the growth rate
    per step of the number of sequences of the free cell that keep a node out of the locked ones
    (`lock_word.avoid_growth`). Once column k repeats b, column k + width + 1 keeps every node out of them, so its
    topological entropy is at most the base-2 logarithm of the growth rate."""
    from computations.lock_word import avoid_growth
    locked, _ = lock_info(block, width)  # (p n,)
    values, _ = steering(block, width)
    return float(locked.mean()), len(values), avoid_growth(block, locked.reshape(len(block), 1 << width))


def longest_run(block: str) -> int:
    """The longest run of equal values in the block, read cyclically."""
    if len(set(block)) == 1:
        return len(block)
    start = next(i for i in range(len(block)) if block[i] != block[i - 1])
    word = block[start:] + block[:start]  # a rotation that starts a run
    return max(len(list(run)) for _, run in itertools.groupby(word))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--periods", default="4,8,10,11,12")
    parser.add_argument("--width", type=int, default=13)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--profile", action="store_true", help="also profile the blocks the game does not exclude")
    parser.add_argument("--lean", action="store_true",
                        help="instead print the entries of LockBlocks11 and 12, leaving out the blocks the kit excludes")
    args = parser.parse_args()
    periods = [int(p) for p in args.periods.split(",")]
    found = survey(periods, args.width, args.workers)
    kit = game.kit_blocks(max(periods))
    for period, blocks in found.items():
        rest = [b for b in blocks if game.bad_pairs(b, 14) > 0]
        if args.lean:
            print("\n".join(lean_entry(b) for b in rest if b not in kit))
            continue
        print(f"period {period}: {len(blocks)} blocks with locks every node can reach at width {args.width}, "
              f"{len(blocks) - len(rest)} of them excluded by the game; the others, with their longest runs: "
              + ", ".join(f"{b} ({longest_run(b)}{', excluded by the kit' if b in kit else ''})" for b in rest))
        if args.profile:
            for b in rest:
                share, length, growth = profile(b, args.width)
                print(f"  {b}: longest run {longest_run(b)}, locked {share:.4f}, steering {length} values, "
                      f"growth {growth:.6f}, entropy at most {np.log2(growth):.5f}")


if __name__ == "__main__":
    main()
