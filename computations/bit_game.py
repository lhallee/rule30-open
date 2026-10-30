"""The finite game decided by sets of nodes, as `Rule30Open.Columns.BitGame` decides it in the kernel.

`criterion` runs the check of `BitGame.gameCheck` on the game graph of `computations/game.py`: the nodes reached after
`D` images of everything, then, at each phase where both values of the column left of the repeating one occur, rounds
that keep the nodes of each value reachable from and reaching the other value's nodes, until one side is empty.
`BitTables` holds the same sets as integers, one bit per node with the column and the free cell as two extra index
bits, and computes images and preimages with the shifts and masks of the Lean module.

    python -m computations.bit_game   # the seven blocks left out of the certificates, with their parameters
    python -m computations.bit_game --max-period 16   # every block the game excludes, about 20 min
    python -m computations.bit_game --phases 17,18   # the phase checks of BitPhases.lean, under a minute
    python -m computations.bit_game --phases 19   # those of BitPhases19.lean
    python -m computations.bit_game --phases 20   # those of BitPhases20.lean
    python -m computations.bit_game --phases 21   # those of BitPhases21.lean, about two and a half minutes

`phase_rounds` gives, for `BitPhases.phaseCheck`, the rounds each phase needs with no images at all; one kernel check
per phase keeps the kernel's tables of one phase at a time.
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


# The 75 blocks of period 17 to 21 that the game excludes, that neither the kit nor WallSets excludes, and that need 13
# or 14 cells, with that least width (findings/columns/game-blocks-18.md, game-blocks-20.md and game-blocks-21.md).
WIDE = {"00000000000101101": 13, "00000000000111011": 14, "00000000011011111": 13, "00000000101110101": 13,
        "00000000110110111": 13, "00000001011111001": 14, "00000010111101111": 13, "00111001111111101": 13,
        "000000000000000111": 14, "000000000010000101": 13, "000000000010010001": 14, "000001011111111001": 14,
        "000010111111110111": 14, "000101111111111001": 13, "0000000000001111111": 14, "0000000000101001111": 13,
        "0000000000110101111": 14, "0000000001001010111": 14, "0000000101001111011": 13, "0000001011011000011": 13,
        "0000100111111111111": 13, "0000101111111001001": 13, "0001011100111111011": 14, "0001011111111111001": 13,
        "0010011011111111111": 13, "00000000000000110001": 14, "00000000000001000001": 13, "00000000000001010001": 14,
        "00000000000011000101": 14, "00000000001100101111": 14, "00000000110001111011": 13, "00000001011111100011": 13,
        "00000001101111111011": 14, "00000101111111001001": 14, "00000101111111110111": 14, "00001011111111001001": 14,
        "00010111111111110111": 13, "00100101110011111111": 13, "00101001111111111101": 14, "01111011111111111111": 14,
        "000000000000001000001": 13, "000000000000001010001": 14, "000000000000001111111": 14,
        "000000000000010010001": 14, "000000000000011000101": 13, "000000000000100001111": 13,
        "000000000000100100111": 14, "000000000000101000001": 13, "000000000000110010111": 13,
        "000000000000110100111": 13, "000000000001100100011": 14, "000000000001101100111": 14,
        "000000000011001001011": 14, "000000000100101111011": 14, "000000000111100111111": 14,
        "000000000111110000001": 13, "000000001001011111011": 13, "000000001011100111011": 14,
        "000000001101100111011": 14, "000000010111111100111": 14, "000000101110011111011": 14,
        "000001101111111111001": 14, "000011111100111111111": 14, "000011111110011111111": 14,
        "000101111111110110011": 13, "000101111111111011001": 13, "000111110101111111111": 13,
        "000111111001111111111": 13, "000111111111100111111": 14, "000111111111110110011": 13,
        "001011111111111110111": 13, "001101001111111111011": 13, "001111010011111111111": 14,
        "001111111111101111111": 14, "010111110111111111111": 14}


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


def phase_rounds(block: str, width: int) -> list[int]:
    """The rounds that the refinement of `BitPhases.phaseCheck` needs at each phase with no images (`D = 0`): it starts
    from every node of the phase, split by the value of the left column, and keeps the nodes of each value that reach
    and are reached by nodes of the other value until one side is empty. Raises if a side never empties at some phase,
    which happens exactly when the game does not exclude the block at this width."""
    source, target, _, _, column = game.game_graph(block, width)  # (2 p n,), (2 p n,), (p n,)
    nodes = column.size
    phase_of = np.arange(nodes) >> width  # (p n,)

    def close(seed: np.ndarray, src: np.ndarray, tgt: np.ndarray) -> np.ndarray:
        found = np.zeros(nodes, dtype=bool)  # (p n,)
        frontier = seed.copy()  # (p n,)
        while frontier.any():
            reached = np.zeros(nodes, dtype=bool)  # (p n,)
            reached[tgt[frontier[src]]] = True
            frontier = reached & ~found
            found |= frontier
        return found

    rounds = []
    for phase in range(len(block)):
        here = phase_of == phase  # (p n,)
        ones, zeros = here & column, here & ~column  # (p n,), (p n,)
        count = 0
        while ones.any() and zeros.any():
            fz, fo = close(zeros, source, target), close(ones, source, target)
            bz, bo = close(zeros, target, source), close(ones, target, source)
            new_zeros, new_ones = zeros & fo & bo, ones & fz & bz
            if (new_zeros == zeros).all() and (new_ones == ones).all():
                raise ValueError(f"{block} at width {width}: both values stay at phase {phase}")
            zeros, ones = new_zeros, new_ones
            count += 1
        rounds.append(count)
    return rounds


def lean_block(block: str, width: int) -> str:
    """The checks of one block in a `BitPhases` module: one kernel check of `phaseCheck` per phase, with no images, the
    rounds of `phase_rounds` and fuel 300, and one theorem that gathers them."""
    period, word = len(block), f"(wordOf {len(block)} 0b{block})"
    rounds = phase_rounds(block, width)
    out = [f"set_option maxHeartbeats 0 in\ntheorem w{block}_{phase} : phaseCheck {word} {width} 0 {count} 300 {phase} = "
           f"true := by\n  decide +kernel\n" for phase, count in enumerate(rounds)]
    cases = "".join(f"  | {phase}, _ => ⟨0, {count}, 300, w{block}_{phase}⟩\n" for phase, count in enumerate(rounds))
    out.append(f"/-- Every phase of `{block}` at width {width}. -/\ntheorem w{block} : ∀ φ, φ < {period} → ∃ D rounds "
               f"fuel,\n    phaseCheck {word} {width} D rounds fuel φ = true\n{cases}"
               f"  | _ + {period}, h => absurd h (by omega)\n")
    return "\n".join(out)


def lean_phases(blocks: dict[str, int], name: str) -> str:
    """The checks of one `BitPhases` module: those of `lean_block` for each block, then the list `name` of the blocks
    with their widths and the theorem that every entry of the list has its checks."""
    out = [lean_block(block, width) for block, width in tqdm(blocks.items(), desc="blocks", file=sys.stderr)]
    entries = [f"(({len(block)}, 0b{block}), {width})" for block, width in blocks.items()]
    lines, line = [], "    "
    for k, entry in enumerate(entries):
        piece = entry + (", " if k + 1 < len(entries) else "]")
        if len(line) + len(piece.rstrip()) > 120:
            lines.append(line.rstrip())
            line = "    "
        line += piece
    lines.append(line)
    alternatives = " | ".join(["rfl"] * len(blocks))
    names = "".join(f"  · exact w{block}\n" for block in blocks)
    out.append(f"/-- The blocks of this module, each as its least rotation `wordOf n bits`, with the width of its checks. -/\n"
               f"def {name} : List ((Nat × Nat) × Nat) := [\n" + "\n".join(lines) + "\n")
    out.append(f"theorem {name}_phases : ∀ e ∈ {name}, ∀ φ, φ < e.1.1 → ∃ D rounds fuel,\n"
               f"    phaseCheck (wordOf e.1.1 e.1.2) e.2 D rounds fuel φ = true := by\n"
               f"  intro e he\n  simp only [{name}, List.mem_cons, List.not_mem_nil, or_false] at he\n"
               f"  rcases he with {alternatives}\n{names}")
    return "\n".join(out)


def wrap_items(items: list[str], indent: str = "    ", width: int = 120) -> str:
    """Comma-separated items wrapped at `width`, closed by a bracket, as the lists of the Lean modules are."""
    lines, line = [], indent
    for k, item in enumerate(items):
        piece = item + (", " if k + 1 < len(items) else "]")
        if len(line) + len(piece.rstrip()) > width:
            lines.append(line.rstrip())
            line = indent
        line += piece
    lines.append(line)
    return "\n".join(lines)


def lean_bit_blocks(period: int, name: str, rows: list[tuple[str, int, int, int]], walls: list[str]) -> str:
    """The body of a BitBlocks module: the list `blocks<name>` of the rows (block, width, images D, rounds) with fuel
    300, one kernel check of `gameCheck` per block, the theorem that gathers them and the exclusions, and, when `walls`
    is not empty, the list `wallBlocks<period>` of blocks that `WallSets.wallSet` accepts, with its exclusion."""
    lst, n = f"blocks{name}", len(rows)
    entries = [f"(({period}, 0b{block}), ({width}, {steps}, {rounds}, 300))" for block, width, steps, rounds in rows]
    text = (f"def {lst} : List ((Nat × Nat) × (Nat × Nat × Nat × Nat)) := [\n{wrap_items(entries)}\n\n"
            "set_option Elab.async false\n")
    for block, width, steps, rounds in rows:
        text += (f"\nset_option maxHeartbeats 0 in\ntheorem check_{block} :\n    gameCheck (Rule30StripCertificateTable.wordOf "
                 f"{period} 0b{block}) {width} {steps} {rounds} 300 = true := by decide +kernel\n")
    lines, line = [], "    "
    for k in range(n):
        piece = "rfl" + (" | " if k + 1 < n else "")
        if len(line) + len(piece.rstrip()) > 118:
            lines.append(line.rstrip())
            line = "    "
        line += piece
    lines.append(line)
    patterns = "\n".join(lines)
    text += (f"\ntheorem {lst}_check : ∀ e ∈ {lst},\n    gameCheck (Rule30StripCertificateTable.wordOf e.1.1 e.1.2) "
             f"e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = true := by\n  intro e he\n  simp only [{lst}, List.mem_cons, "
             f"List.mem_nil_iff, or_false] at he\n  rcases he with\n{patterns}\n"
             + "".join(f"  · exact check_{block}\n" for block, *_ in rows))
    if walls:
        text += (f"\n/-- The blocks of period {period} that the game excludes and the kit does not, and that `WallSets` "
                 f"excludes, each as its least\nrotation `wordOf {period} bits`. -/\ndef wallBlocks{period} : List Nat := [\n"
                 + wrap_items([f"0b{block}" for block in walls]) + "\n\n"
                 f"theorem wallBlocks{period}_all : wallBlocks{period}.all (fun bits => wallSet "
                 f"(Rule30StripCertificateTable.wordOf {period} bits)) = true := by\n  decide +kernel\n\n"
                 f"/-- **The blocks of `WallSets`**: for each entry of `wallBlocks{period}`, the center column does not "
                 f"repeat the block from any\ntime `T` on. -/\ntheorem center_not_wallBlocks{period} (bits : Nat) "
                 f"(hb : bits ∈ wallBlocks{period}) (T : Nat)\n    (hcol : ∀ t : Nat, T ≤ t → Rule30Prize.center t = "
                 f"cyc (Rule30StripCertificateTable.wordOf {period} bits) (t - T)) :\n    False :=\n  "
                 f"center_wall_set_block T _ (List.all_eq_true.1 wallBlocks{period}_all bits hb) hcol\n")
    text += (f"\n/-- **The {n} blocks**: for each entry of `{lst}`, the center column is not, from any time `T` on, the "
             f"block\n`wordOf {period} bits`, read from any phase. -/\ntheorem center_not_{lst} (e : (Nat × Nat) × "
             f"(Nat × Nat × Nat × Nat)) (he : e ∈ {lst}) (T shift : Nat)\n    (h : ∀ t : Nat, T ≤ t → "
             f"Rule30Prize.center t =\n      (Rule30StripCertificateTable.wordOf e.1.1 e.1.2).getD ((t + shift) % "
             f"e.1.1) false) : False :=\n  center_not_bitGame _ _ _ _ _ ({lst}_check e he) T shift fun t ht => by\n"
             f"    rw [h t ht, Rule30StripCertificateTable.wordOf_length]\n\n/-- The same in the kit's form: none of "
             f"the {n} blocks is an `EventuallyWord` of the center column. -/\ntheorem not_eventually_{lst} (e : "
             f"(Nat × Nat) × (Nat × Nat × Nat × Nat)) (he : e ∈ {lst}) :\n    ¬ Rule30StripCertificates.EventuallyWord "
             f"(Rule30StripCertificateTable.wordOf e.1.1 e.1.2) :=\n  bitGame_not_eventuallyWord _ _ _ _ _ "
             f"({lst}_check e he)\n")
    return text


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
    parser.add_argument("--phases", type=str, default="",
                        help="print the phase checks of the blocks of WIDE of these periods, comma separated")
    args = parser.parse_args()
    if args.phases:
        periods = [int(period) for period in args.phases.split(",")]
        chosen = {block: width for block, width in WIDE.items() if len(block) in periods}
        print(lean_phases(chosen, f"blocksPhases{max(periods)}"))
        return
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
