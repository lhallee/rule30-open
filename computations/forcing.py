"""Which column words fix the cell right of the column, whatever lies to the right?

A word u of n values of column k, read at times t - n, ..., t - 1, forces cell k + 1 at time t when that cell is the
same for every start of cells k + 1, ..., k + n + 1 at time t - n; cells farther right cannot reach it in time. Nine 1s
and then a 0 force it (the wall of `Rule30Open.Columns.LongRuns`), and so do words with 0s inside and no long run.

Forcing is what the wall arguments use at the 0s of a repeating column: if the column repeats a block and the block's
history before each of its 0s forces cell k + 1, the column left of it repeats too, which the adjacent-column theorem
forbids. `forcing_family` runs that test on every primitive block, with the exact forcing words of one length.

    python -m computations.forcing --length 20 --max-period 20   # about 2 min
"""

from __future__ import annotations

import argparse
import sys

import numpy as np
from tqdm.auto import tqdm

from computations.wall_segments import in_set_family, necklaces


def step_set(configs: np.ndarray, cells: int, col: int) -> np.ndarray:
    """The set of configurations of `cells - 1` cells one step after `configs`, beside a column reading `col`.

    `configs` has shape (s,): configurations of `cells` cells right of the column, bit j for cell k + 1 + j. The last
    cell only feeds the OR of the one before it, so the image has one cell fewer."""
    mask = (1 << (cells - 1)) - 1
    left = ((configs << 1) | col) & mask  # (s,) bit j holds cell k + j, the column at bit 0
    middle = configs & mask  # (s,)
    right = (configs >> 1) & mask  # (s,)
    seen = np.zeros(1 << (cells - 1), dtype=bool)  # (2^(cells - 1),)
    seen[left ^ (middle | right)] = True
    return np.flatnonzero(seen)


def forcing_words(n: int) -> dict[str, int]:
    """Every word of length `n` that forces cell k + 1, with the value it forces: a depth-first search over the word
    from its first value, carrying the exact set of configurations of the cells that can still reach cell k + 1."""
    out: dict[str, int] = {}
    stack: list[tuple[str, np.ndarray]] = [("", np.arange(1 << (n + 1), dtype=np.int64))]  # (word, configs (s,))
    bar = tqdm(total=1 << n, desc=f"words of length {n}", unit="word", file=sys.stderr, mininterval=5,
               disable=n < 16)
    while stack:
        word, configs = stack.pop()
        if len(word) == n:
            values = np.unique(configs & 1)
            if len(values) == 1:
                out[word] = int(values[0])
            bar.update(1)
            continue
        cells = n + 1 - len(word)
        for col in (0, 1):
            stack.append((word + str(col), step_set(configs, cells, col)))
    bar.close()
    return out


def forced_value(word: str) -> int | None:
    """The value `word` forces on cell k + 1, or None: brute force over every start of the n + 1 cells that can reach
    it, one row per start, independent of `forcing_words`."""
    n = len(word)
    starts = np.arange(1 << (n + 1), dtype=np.int64)  # (2^(n + 1),)
    cells = ((starts[:, None] >> np.arange(n + 1)) & 1).astype(np.uint8)  # (2^(n + 1), n + 1), cell k + 1 + j at j
    for ch in word:
        left = np.concatenate([np.full((len(cells), 1), int(ch), dtype=np.uint8), cells[:, :-1]], axis=1)  # (s, n + 1)
        right = np.concatenate([cells[:, 1:], np.zeros((len(cells), 1), dtype=np.uint8)], axis=1)  # (s, n + 1)
        cells = left ^ (cells | right)
    values = np.unique(cells[:, 0])
    return int(values[0]) if len(values) == 1 else None


def lookback(block: str, phase: int, n: int) -> str:
    """The `n` values of a column repeating `block` just before `phase`, read cyclically."""
    return "".join(block[(phase - n + j) % len(block)] for j in range(n))


def excluded(block: str, words: dict[str, int], n: int) -> bool:
    """Whether the `n` values before each 0 of `block`, read cyclically, form a forcing word."""
    return all(lookback(block, phase, n) in words for phase, ch in enumerate(block) if ch == "0")


def longest_runs(block: str) -> tuple[float, float]:
    """The longest run of 1s and of 0s of `block`, read cyclically; a constant block has an infinite run."""
    doubled = block * 2
    ones = max(len(run) for run in doubled.split("0")) if "0" in block else float("inf")
    zeros = max(len(run) for run in doubled.split("1")) if "1" in block else float("inf")
    return ones, zeros


def forcing_family(words: dict[str, int], n: int, max_period: int) -> dict[int, list[str]]:
    """The primitive blocks of each period up to `max_period` that `excluded` accepts with the forcing words of
    length `n`."""
    return {period: [block for block in necklaces(period) if excluded(block, words, n)]
            for period in tqdm(range(1, max_period + 1), desc="periods", file=sys.stderr, mininterval=5)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--length", type=int, default=20, help="the longest forcing words computed")
    parser.add_argument("--max-period", type=int, default=20)
    parser.add_argument("--game", action="store_true",
                        help="also run the finite game at width 6 on the excluded blocks without nine 1s in a row")
    args = parser.parse_args()

    previous: dict[str, int] = {}
    words: dict[str, int] = {}
    for n in range(1, args.length + 1):
        words = forcing_words(n)
        minimal = sorted(word for word in words if word[1:] not in previous)
        shown = f": {', '.join(f'{w} -> {words[w]}' for w in minimal)}" if 0 < len(minimal) <= 10 else ""
        print(f"length {n}: {len(words)} forcing words ({len(words) / 2 ** n:.4f} of all), {len(minimal)} with no "
              f"shorter forcing suffix, {sum('1' * 9 not in w for w in minimal)} of those without nine 1s{shown}")
        previous = words

    family = forcing_family(words, args.length, args.max_period)
    total = 0
    others: list[str] = []
    for period, blocks in family.items():
        nine = [b for b in blocks if "1" * 9 in b + b or b == "1"]
        sets = {b for b in necklaces(period) if in_set_family(b)}
        total += len(blocks)
        others += [b for b in blocks if b not in nine]
        print(f"period {period}: {len(blocks)} blocks, {len(nine)} with nine 1s in a row "
              f"({'the same' if set(nine) == sets else 'not the same'} as the sets of windows)")
    print(f"up to period {args.max_period}: {total} blocks; {len(others)} without nine 1s in a row: {others}")
    runs = [longest_runs(b) for blocks in family.values() for b in blocks]
    print(f"every block has a run of at least {min(ones for ones, zeros in runs if zeros < 9)} 1s or of at least "
          f"9 0s")
    if args.game:
        from computations import game
        width = {b: next((w for w in (6, 10) if game.bad_pairs(b, w) == 0), None) for b in others}
        print(f"the game excludes {sum(w is not None for w in width.values())} of the {len(others)} at width 6 or 10: "
              f"{width}")


if __name__ == "__main__":
    main()
