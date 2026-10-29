"""The finite game decided by sets of nodes, as `Rule30Open.Columns.BitGame` decides it in the kernel.

`criterion` runs the check of `BitGame.gameCheck` on the game graph of `computations/game.py`: the nodes reached after
`D` images of everything, then, at each phase where both values of the column left of the repeating one occur, rounds
that keep the nodes of each value reachable from and reaching the other value's nodes, until one side is empty.
`BitTables` holds the same sets as integers, one bit per node with the column and the free cell as two extra index
bits, and computes images and preimages with the shifts and masks of the Lean module.

    python -m computations.bit_game   # the seven blocks left out of the certificates, with their parameters
    python -m computations.bit_game --max-period 16   # every block the game excludes, about 20 min
"""

from __future__ import annotations

import argparse
import sys

import numpy as np
from tqdm.auto import tqdm

from computations import game

# The seven blocks of period at most 16 that the game excludes and the certificates of GameBlocks, GameBlocksLong and
# the kit leave out, with the least width at which the game excludes each.
SEVEN = {"00000001001111": 13, "00000000010001": 14, "000000000101101": 14, "000001011111011": 14,
         "0000001011111011": 12, "0000101111111011": 13, "0001011111111001": 14}


def criterion(block: str, width: int, steps: int | None = None) -> tuple[bool, int, int, int]:
    """The check of `BitGame.gameCheck` on the game graph: whether it decides `block` at `width`, the number of images
    `D` (until the set of reached nodes stops changing when `steps` is None), the most rounds at a phase, and the
    longest closure, in steps."""
    source, target, _, _, column = game.game_graph(block, width)  # (2 p n,), (2 p n,), (p n,)
    nodes = column.size
    reached = np.ones(nodes, dtype=bool)  # (p n,)
    count = 0
    while steps is None or count < steps:
        image = np.zeros(nodes, dtype=bool)  # (p n,)
        image[target[reached[source]]] = True
        count += 1
        if steps is None and (image == reached).all():
            break
        reached = image
    phase_of = np.arange(nodes) >> width  # (p n,)
    longest = [0]

    def close(seed: np.ndarray, src: np.ndarray, tgt: np.ndarray) -> np.ndarray:
        found = np.zeros(nodes, dtype=bool)  # (p n,)
        frontier = seed.copy()  # (p n,)
        length = 0
        while frontier.any():
            nxt = np.zeros(nodes, dtype=bool)  # (p n,)
            nxt[tgt[frontier[src]]] = True
            frontier = nxt & ~found
            found |= frontier
            length += 1
        longest[0] = max(longest[0], length)
        return found

    most = 0
    for phase in range(len(block)):
        here = reached & (phase_of == phase)  # (p n,)
        ones, zeros = here & column, here & ~column  # (p n,), (p n,)
        rounds = 0
        while ones.any() and zeros.any():
            fz, fo = close(zeros, source, target), close(ones, source, target)
            bz, bo = close(zeros, target, source), close(ones, target, source)
            new_zeros, new_ones = zeros & fo & bo, ones & fz & bz
            rounds += 1
            if (new_zeros == zeros).all() and (new_ones == ones).all():
                return False, count, rounds, longest[0]
            zeros, ones = new_zeros, new_ones
        most = max(most, rounds)
    return True, count, most, longest[0]


class BitTables:
    """The sets of the Lean module as integers: bit `phase * 2^(K + 2) + z` for the node of that phase whose cells are
    the low `K` bits of `z`, a set of cell words held the same over index bits `K` and `K + 1`."""

    def __init__(self, block: str, width: int) -> None:
        self.block = [int(ch) for ch in block]
        self.period, self.width = len(block), width
        self.size = 1 << (width + 2)  # bits per block
        self.total = self.period * self.size
        self.full = (1 << self.total) - 1
        index = np.arange(self.total, dtype=np.int64)  # (p 2^(K+2),)
        self.pat = [self._pack(((index >> s) & 1).astype(bool)) for s in range(width + 2)]
        self.npat = [self.full ^ p for p in self.pat]
        col = np.array(self.block, dtype=bool)[index >> (width + 2)]  # (p 2^(K+2),)
        self.colmask = self._pack(((index >> width) & 1).astype(bool) == col)

    @staticmethod
    def _pack(bits: np.ndarray) -> int:
        """The integer with bit i set where `bits[i]`; `bits` has shape (n,)."""
        return int.from_bytes(np.packbits(bits.astype(np.uint8), bitorder="little").tobytes(), "little")

    def ds(self, table: int, mask: int, d: int) -> int:
        """The delta swap of `BitGame.ds`."""
        x = ((table >> d) ^ table) & mask
        return table ^ x ^ (x << d)

    def proj(self, table: int, p: int) -> int:
        return table | ((table >> (1 << p)) & self.npat[p]) | ((table & self.npat[p]) << (1 << p))

    def canon(self, table: int) -> int:
        k = self.width
        return self.proj(self.proj(table & self.npat[k] & self.npat[k + 1], k), k + 1)

    def flips(self, table: int, order: range) -> int:
        k = self.width
        for j in order:
            t, a, b = (k if j == 0 else j - 1), j, (k + 1 if j + 1 == k else j + 1)
            table = self.ds(table, self.npat[t] & (self.pat[a] | self.pat[b]), 1 << t)
        return table

    def swaps(self, table: int, order: range) -> int:
        for i in order:
            table = self.ds(table, self.pat[i] & self.npat[i + 1], 1 << i)
        return table

    def post(self, table: int) -> int:
        """`BitGame.post`: the image of a set of nodes, for both free cells."""
        k = self.width
        t = self.flips(self.canon(table) & self.colmask, range(k))
        t = self.swaps(self.proj(self.proj(t, k - 1), k + 1), range(k - 1, -1, -1))
        top = (self.period - 1) * self.size
        t &= self.full
        return self.canon(((t << self.size) & self.full) | (t >> top))

    def pre(self, table: int) -> int:
        """`BitGame.pre`: the nodes with some move into the set."""
        k = self.width
        t = self.canon(table) & self.full
        top = (self.period - 1) * self.size
        t = (t >> self.size) | ((t << top) & self.full)
        t = self.flips(self.swaps(t, range(k)), range(k - 1, -1, -1)) & self.colmask
        return self.canon(self.proj(self.proj(t, k + 1), k))

    def nodes(self, table: int) -> np.ndarray:
        """The canonical bits of a table as a node set of shape (p 2^K,), in the order of `game.game_graph`."""
        out = np.zeros(self.period << self.width, dtype=bool)  # (p 2^K,)
        for phase in range(self.period):
            for r in range(1 << self.width):
                out[(phase << self.width) + r] = (table >> (phase * self.size + r)) & 1
        return out

    def table(self, nodes: np.ndarray) -> int:
        """A node set of shape (p 2^K,) as a canonical table."""
        out = 0
        for node in np.flatnonzero(nodes).tolist():
            phase, r = divmod(node, 1 << self.width)
            out |= 1 << (phase * self.size + r)
        return self.canon(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-period", type=int, default=0,
                        help="instead of the seven blocks, every block the game excludes up to this period")
    args = parser.parse_args()
    if not args.max_period:
        for block, width in SEVEN.items():
            ok, steps, rounds, longest = criterion(block, width)
            print(f"{block} at width {width}: decided {ok}, D = {steps}, rounds {rounds}, longest closure {longest}")
        return
    excluded = decided = 0
    worst = (0, 0, 0)
    for period in range(1, args.max_period + 1):
        for block in tqdm(game.necklaces(period), desc=f"period {period}", file=sys.stderr, mininterval=5):
            top = next((w for w in (6, 10, 14) if game.bad_pairs(block, w) == 0), None)
            if top is None:
                continue
            width = next(w for w in range(1, top + 1) if game.bad_pairs(block, w) == 0)
            ok, steps, rounds, longest = criterion(block, width)
            excluded += 1
            decided += ok
            worst = (max(worst[0], steps), max(worst[1], rounds), max(worst[2], longest))
    print(f"up to period {args.max_period}: the game excludes {excluded} blocks, the check decides {decided} of them at "
          f"the least width; at most D = {worst[0]}, {worst[1]} rounds, closures of {worst[2]} steps")


if __name__ == "__main__":
    main()
