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
whether every node can reach them; `mixed_nodes` computes that complement backward, for wider games. `survey` runs
`lock_info` on every primitive block of the given periods.

    python -m computations.locks --periods 4,8,10,11,12 --width 13 --workers 3   # about 3 min
    python -m computations.locks --profile --workers 3   # adds about 2 min
    python -m computations.locks --lean --workers 3   # the entries of LockBlocks11 and LockBlocks12
    python -m computations.locks --periods 2,3,5,6,7,9 --census 13,16 --workers 3   # no locked node, about 2 min
    python -m computations.locks --periods 6 --census 20,22 --repeat 2 --wide   # none modulo 12 either, about 15 min
    python -m computations.locks --white 4,5,6,7,8,9,10,11,12,13,14,15,16 --workers 3   # white runs, about 40 min
    python -m computations.locks --reach 0000010111001 --width 18   # the share of nodes that can reach a lock, 20 s
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


def back_search(word: str, width: int, seen: np.ndarray) -> np.ndarray:
    """The nodes of the game of `word` at `width` cells from which some values of the cell beyond reach the nodes
    `seen`, found backward from them (`predecessors`), in time proportional to their number and one byte per node of
    the game; `seen` is filled in place."""
    # seen: (p n,)
    frontier = np.flatnonzero(seen)  # (f,)
    fresh = np.zeros(seen.size, dtype=bool)  # (p n,), the nodes found in one round, cleared after it
    while frontier.size:
        before = predecessors(word, width, frontier.astype(np.uint64)).astype(np.int64)  # (m,)
        fresh[before[~seen[before]]] = True
        frontier = np.flatnonzero(fresh)  # (f,), each once, in order
        fresh[frontier] = False
        seen[frontier] = True
    return seen  # (p n,)


def sparse_search(word: str, width: int, start: np.ndarray, cap: int) -> np.ndarray | None:
    """The nodes of the game of `word` at `width` cells, up to 58, from which some values of the cell beyond reach the
    nodes `start` (phase * 2^width + window), found backward as `back_search` finds them but holding only the nodes
    found, in increasing order: for games too wide for a byte per node, when few nodes can reach. None once more than
    `cap` are found."""
    # start: (s,)
    seen = np.unique(start.astype(np.uint64))  # (v,)
    frontier = seen
    while frontier.size:
        before = np.unique(predecessors(word, width, frontier))  # (m,)
        frontier = before[~np.isin(before, seen, assume_unique=True)]  # (f,)
        seen = np.union1d(seen, frontier)  # (v,)
        if seen.size > cap:
            return None
    return seen  # (v,)


def predecessors(word: str, width: int, keys: np.ndarray) -> np.ndarray:
    """The nodes of the game of `width` cells with a move to one of the nodes `keys` (phase * 2^width + window), with
    repeats. The rule is permutive in its left cell, so the old cell `width` and the cell beyond it fix the old window
    from the right, cell by cell, and the old cell 0 must then be the column's value at the phase before."""
    # keys: (k,)
    one, period = np.uint64(1), len(word)
    window = keys & np.uint64((1 << width) - 1)  # (k,)
    before = ((keys >> np.uint64(width)).astype(np.int64) - 1) % period  # (k,)
    column = np.array([int(bit) for bit in word], dtype=np.uint64)[before]  # (k,)
    found = []
    for last in (0, 1):
        for beyond in (0, 1):
            right = np.full(keys.shape, beyond, dtype=np.uint64)  # (k,), the old cell i + 1
            cell = np.full(keys.shape, last, dtype=np.uint64)  # (k,), the old cell i
            old = cell << np.uint64(width - 1)  # (k,)
            for i in range(width, 0, -1):
                left = ((window >> np.uint64(i - 1)) & one) ^ (cell | right)  # (k,), the old cell i - 1
                if i > 1:
                    old |= left << np.uint64(i - 2)
                right, cell = cell, left
            ok = cell == column  # (k,)
            found.append(before[ok].astype(np.uint64) << np.uint64(width) | old[ok])
    return np.concatenate(found)  # (m,)


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


def fewest_mixed(block: str, width: int) -> int:
    """The least number of phases, over the nodes, at which a node can reach both values of the column left of the
    repeating one: 0 exactly when some node is locked."""
    source, target, _, _, column = game.game_graph(block, width)  # (2 p n,), (2 p n,), _, _, (p n,)
    phase = np.arange(column.size) >> width  # (p n,)
    count = np.zeros(column.size, dtype=np.int64)  # (p n,)
    for ph in range(len(block)):
        here = phase == ph  # (p n,)
        count += back_closure(here & column, source, target) & back_closure(here & ~column, source, target)
    return int(count.min())


def steerable(block: str, width: int) -> bool:
    """Whether some node is locked and every node can be steered into a locked node."""
    locked, reach = lock_info(block, width)  # (p n,), (p n,)
    return bool(locked.any() and reach.all())


def mixed_nodes(block: str, width: int) -> np.ndarray:
    """The nodes that can reach both values of the left column at one phase, the complement of `lock_info`'s locked
    nodes, found backward from each white phase's nodes by `back_search`: one byte per node and no list of moves, for
    games of 20 cells and more. It stops once every node is mixed, which for a block without a locked node is often
    after its first white phase."""
    period, size = len(block), 1 << width
    c = np.array([int(bit) for bit in block], dtype=np.uint8)  # (p,)
    first = (np.arange(size) & 1).astype(np.uint8)  # (n,), cell 1 of each window
    mixed = np.zeros(period * size, dtype=bool)  # (p n,)
    for ph in np.flatnonzero(c == 0):  # at a black phase the block alone fixes the left column
        left = c[(ph + 1) % period] ^ first  # (n,), the left column at this white phase
        both = np.ones(period * size, dtype=bool)  # (p n,)
        for value in (0, 1):
            seed = np.zeros(period * size, dtype=bool)  # (p n,)
            seed[ph * size:(ph + 1) * size] = left == value
            both &= back_search(block, width, seed)
        mixed |= both
        if mixed.all():
            break
    return mixed  # (p n,)


def has_lock(block: str, width: int, wide: bool = False) -> bool:
    """Whether some node of the game at this width is locked, by `lock_info`, or by `mixed_nodes` when `wide`."""
    if wide:
        return not bool(mixed_nodes(block, width).all())
    locked, _ = lock_info(block, width)  # (p n,)
    return bool(locked.any())


def lock_census(periods: list[int], widths: list[int], repeat: int = 1, workers: int = 1,
                wide: bool = False) -> dict[tuple[int, int], list[str]]:
    """For each period and width, the primitive blocks b of that period whose game for b repeated `repeat` times has a
    locked node (`has_lock`, with `wide` as given). A lock for the repeated block makes the column left of the
    repeating one eventually periodic with `repeat` times the period of b, which Jen's theorem forbids as well."""
    found = {}
    for period in periods:
        blocks = game.necklaces(period)
        for width in widths:
            task = functools.partial(has_lock, width=width, wide=wide)
            repeated = [block * repeat for block in blocks]
            progress = functools.partial(tqdm, total=len(blocks), desc=f"period {period}, width {width}",
                                         file=sys.stderr, mininterval=5)
            if workers > 1:
                with multiprocessing.get_context("spawn").Pool(workers) as pool:
                    flags = list(progress(pool.imap(task, repeated, chunksize=1)))
            else:
                flags = [task(block) for block in progress(repeated)]
            found[(period, width)] = [block for block, flag in zip(blocks, flags) if flag]
    return found


def family(template: str, k: int) -> str:
    """The block of a family written as space-separated parts, each a literal word or `w^k` for w repeated k times."""
    return "".join(part[:-2] * k if part.endswith("^k") else part for part in template.split())


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


def finals_of(block: str, width: int, values: list[int]) -> dict[int, list[int]]:
    """The windows where the sequence `values` of the free cell leaves the windows started at each phase, by final
    phase."""
    from computations.lock_certificate import successor_table
    period = len(block)
    successors = successor_table(block, width)  # (p, 2, 2^W)
    finals: dict[int, set[int]] = {}
    for start in range(period):
        windows = np.arange(1 << width, dtype=np.int64)  # (2^W,)
        for step, value in enumerate(values):
            windows = successors[(start + step) % period, value][windows]  # (2^W,)
        finals.setdefault((start + len(values)) % period, set()).update(np.unique(windows).tolist())
    return {phase: sorted(states) for phase, states in sorted(finals.items())}


def steering(block: str, width: int) -> tuple[list[int], dict[int, list[int]]]:
    """A sequence of values of the free cell that brings every node, started at any phase, to a locked node
    (`lock_word.universal_word` with the locked nodes as target), and the windows where it leaves them, by final phase."""
    from computations.lock_word import universal_word
    locked, _ = lock_info(block, width)  # (p n,)
    values = universal_word(block, locked.reshape(len(block), 1 << width))
    return values, finals_of(block, width, values)


def constant_steering(block: str, width: int, value: int) -> int | None:
    """The least number of steps after which the free cell held at `value` has brought every node to a locked node,
    or None if some node never reaches one: with one value the game is a function on the nodes, and the steps are the
    largest distance to the locked nodes backward along it."""
    from computations.lock_certificate import successor_table
    period, size = len(block), 1 << width
    successors = successor_table(block, width)  # (p, 2, 2^W)
    nodes = np.arange(period * size)  # (p n,)
    after = ((nodes >> width) + 1) % period * size + successors[nodes >> width, value, nodes & (size - 1)]  # (p n,)
    reached, _ = lock_info(block, width)  # (p n,), nodes at distance at most `steps`
    steps = 0
    while not reached.all():
        grown = reached | reached[after]  # (p n,)
        if (grown == reached).all():
            return None
        reached, steps = grown, steps + 1
    return steps


def lean_entry(block: str, values: list[int] | None = None, name: str = "steer") -> str:
    """The Lean entry `LockBlocks.Steered` for one block at width 13, the width `Steered.check` uses: the block, the
    sequence as a number, value i at bit i (`steering`'s unless `values` is given), its length and the final windows
    by phase, with the theorem that the check passes."""
    if values is None:
        values, finals = steering(block, 13)
    else:
        finals = finals_of(block, 13, values)
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
    return (f"def {name}_{block} : Steered := ⟨{len(block)}, 0b{block},\n"
            f"  0x{word:x},\n" + "\n".join(lines) + "\n\n"
            f"set_option maxHeartbeats 0 in\n"
            f"theorem {name}_{block}_check : {name}_{block}.check = true := by decide +kernel\n")


def white_run(block: str, widths: list[int]) -> tuple[int, int] | None:
    """The width at which the fewest white values of the free cell bring every node to a locked node, with that number
    (`constant_steering` with the value 0), the smaller width on a tie; None if white steers at none of the widths."""
    found = [(steps, width) for width in widths if (steps := constant_steering(block, width, 0)) is not None]
    if not found:
        return None
    steps, width = min(found)
    return width, steps


def lean_white_entry(block: str, width: int) -> str:
    """The Lean entry `LockBlocks.WhiteRun` for one block: the block, the width, the number of white values that steer
    and the final windows by phase, with the theorem that the check passes."""
    steps = constant_steering(block, width, 0)
    assert steps is not None
    finals = finals_of(block, width, [0] * steps)
    groups = ", ".join(f"({phase}, [{', '.join(map(str, states))}])" for phase, states in finals.items())
    lines = [f"  {width}, {steps}, "]
    for k, item in enumerate(f"[{groups}]⟩".split(", ")):
        piece = item if k == 0 else ", " + item
        if len(lines[-1]) + len(piece) > 119:
            lines[-1] += ","
            lines.append("    " + item)
        else:
            lines[-1] += piece
    return (f"def white_{block} : WhiteRun := ⟨{len(block)}, 0b{block},\n" + "\n".join(lines) + "\n\n"
            f"set_option maxHeartbeats 0 in\n"
            f"theorem white_{block}_check : white_{block}.check = true := by decide +kernel\n")


def profile(block: str, width: int) -> tuple[float, int, float]:
    """The fraction of nodes that are locked, the length of the steering sequence of `steering`, and the growth rate
    per step of the number of sequences of the free cell that keep a node out of the locked ones
    (`lock_word.avoid_growth`). Once column k repeats b, column k + width + 1 keeps every node out of them, so its
    topological entropy is at most the base-2 logarithm of the growth rate."""
    from computations.lock_word import avoid_growth
    locked, _ = lock_info(block, width)  # (p n,)
    values, _ = steering(block, width)
    return float(locked.mean()), len(values), avoid_growth(block, locked.reshape(len(block), 1 << width))


def growth(block: str, width: int) -> tuple[float, float]:
    """The fraction of nodes that are locked and the growth rate of `profile`, without the steering sequence, which is
    long to build in the wider games, and with the rate's iteration cut at 5,000 steps (`coin_lock.period_rate`, whose
    value bounds the rate from above wherever the iteration stops)."""
    from computations import coin_lock
    locked, _ = lock_info(block, width)  # (p n,)
    member = locked.reshape(len(block), 1 << width)  # (p, 2^width)
    return float(locked.mean()), 2 * coin_lock.period_rate(block, member, tolerance=1e-10, limit=5000)


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
    parser.add_argument("--growth", action="store_true",
                        help="also give the locked share and growth rate of the blocks nothing excludes (for width 16)")
    parser.add_argument("--lean", action="store_true",
                        help="instead print the entries of LockBlocks11 and 12, leaving out the blocks the kit excludes")
    parser.add_argument("--census", help="instead count, at each of these widths, the blocks with any locked node")
    parser.add_argument("--white", help="also give, over these widths, the shortest white run that steers each block")
    parser.add_argument("--lean-white", action="store_true", help="with --white, print the entries of LockWhite")
    parser.add_argument("--repeat", type=int, default=1, help="with --census, play the game for each block repeated")
    parser.add_argument("--wide", action="store_true",
                        help="with --census, search backward (`mixed_nodes`), for widths of 20 cells and more")
    parser.add_argument("--family", help="instead, with --census, the blocks of a family such as '0^k 11101', k = 0..12")
    parser.add_argument("--mixed", help="instead print, for these blocks at --width, the fewest phases with both values")
    parser.add_argument("--reach", help="instead print, for these blocks at --width, repeated --repeat times, the locked "
                                        "nodes, the share of nodes that can reach one, and whether the white window can")
    args = parser.parse_args()
    periods = [int(p) for p in args.periods.split(",")]
    if args.reach:
        for block in args.reach.split(","):
            locked, reach = lock_info(block * args.repeat, args.width)  # (p n,), (p n,)
            print(f"{block}, repeated {args.repeat} times, width {args.width}: {int(locked.sum())} locked nodes, "
                  f"{reach.mean():.6f} of the nodes can reach one, the white window at phase 0 "
                  f"{'can' if reach[0] else 'cannot'}", flush=True)
        return
    if args.mixed:
        for block in args.mixed.split(","):
            print(f"{block} at width {args.width}: every node can reach both values of the left column at "
                  f"{fewest_mixed(block, args.width)} or more of its {block.count('0')} white phases")
        return
    if args.census and args.family:
        for width in [int(w) for w in args.census.split(",")]:
            blocks = [family(args.family, k) for k in range(13)]
            print(f"{args.family}, width {width}: locked windows at the periods "
                  + ", ".join(str(len(b)) for b in blocks if b and has_lock(b * args.repeat, width)))
        return
    if args.census:
        for period in periods:
            for width in [int(w) for w in args.census.split(",")]:
                blocks = lock_census([period], [width], args.repeat, args.workers, args.wide)[(period, width)]
                print(f"period {period}, repeated {args.repeat} times, width {width}: {len(game.necklaces(period))} "
                      f"blocks, {len(blocks)} with a locked node" + (f": {', '.join(blocks)}" if blocks else ""),
                      flush=True)
        return
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
        if args.white:
            widths = [int(w) for w in args.white.split(",")]
            blocks = [b for b in rest if b not in kit]
            task = functools.partial(white_run, widths=widths)
            if args.workers > 1:
                with multiprocessing.get_context("spawn").Pool(args.workers) as pool:
                    bests = pool.map(task, blocks, chunksize=1)
            else:
                bests = [task(b) for b in tqdm(blocks, desc="white runs", file=sys.stderr)]
            for b, best in zip(blocks, bests):
                if best is not None:
                    print(lean_white_entry(b, best[0]) if args.lean_white else
                          f"  {b}: {best[1]} white values in column {best[0] + 1} steer every window of {best[0]} cells")
        if args.profile:
            for b in rest:
                share, length, rate = profile(b, args.width)
                print(f"  {b}: longest run {longest_run(b)}, locked {share:.4f}, steering {length} values, "
                      f"growth {rate:.6f}, entropy at most {np.log2(rate):.5f}")
        if args.growth:
            blocks = [b for b in rest if b not in kit]
            task = functools.partial(growth, width=args.width)
            if args.workers > 1:
                with multiprocessing.get_context("spawn").Pool(args.workers) as pool:
                    rates = list(tqdm(pool.imap(task, blocks), total=len(blocks), desc="growth", file=sys.stderr))
            else:
                rates = [task(b) for b in tqdm(blocks, desc="growth", file=sys.stderr)]
            for b, (share, rate) in zip(blocks, rates):
                print(f"  {b}: locked {share:.4f}, growth {rate:.9f}, entropy at most {np.log2(rate):.7f}")


if __name__ == "__main__":
    main()
