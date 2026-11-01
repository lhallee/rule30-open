"""Certificates of the finite game with cyclic classes that the Lean kernel checks node by node on small sets.

The column repeats `block` of period P; the game keeps the cells 1 .. W right of it, with cell W + 1 free
(`game.moves`). `bit_game.criterion` decides the class test for `000000001011` at 16 cells on the block read three
times, but its tables do not fit the kernel. This certificate splits the work so that every check is local and runs
over a few tens of thousands of nodes.

1. **Widths one at a time** (`levels`). For w = 1 .. W, let Q_w be the nodes of the width-w game whose first w - 1
   cells lie in Z_(w-1) (Z_0 is everything), and Z_w the set that the images of Q_w settle into. Dropping cell w maps
   a play of width w to a play of width w - 1, and Q_w is closed under moves, so a play whose first w - 1 cells stay in
   Z_(w-1) has its first w cells in Q_w; inside Q_w every node off Z_w has a height, the longest walk from it to Z_w,
   and every move from it lowers the height. So every play enters Z_w and stays there, at every width in turn.
2. **Classes on the last set** (`final_labels`). On Z_W, closed under moves, a node gets a rank (its strongly
   connected component's layer in the condensation, the components that can hold a play kept apart, as in
   `game.game_ranks`) and, in a component that can hold a play, a label: its distance from a root modulo the
   component's cyclic period d. A move never lowers the rank, a move from a transient rank raises it, a move inside a
   component raises the label by one modulo d, and the column left of the repeating one is a function of the rank and
   the label. A play settles in one component and its labels run through 0 .. d - 1 in turn, so the left column is
   eventually periodic, which the adjacent-column theorem excludes.

`check` re-runs the conditions of the Lean module node by node in plain Python; `lean_data` writes the certificate as
the tries of `Rule30Open.Columns.ClassGame` (a node's cells as a key, read from bit 0 at the root).

    python -m computations.class_certificate                       # the sizes for 000000001011 at 16 cells
    python -m computations.class_certificate --lean > data.lean    # the certificate as Lean definitions
"""

from __future__ import annotations

import argparse
import functools
import math
import sys
from dataclasses import dataclass
from graphlib import TopologicalSorter

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import breadth_first_order, connected_components
from tqdm.auto import tqdm

from computations import game


@dataclass
class Certificate:
    """The data of `Rule30Open.ClassCert`: for each width w = 1 .. W the height of every node of Q_w (-1 off Q_w, 0 on
    Z_w), and on Z_W the code rank * base + label of every node (-1 off Z_W), with the transient ranks, each rank's
    modulus and the left column at rank r and label l as bits r, 8 r .. 8 r + 7 and r * base + l of three numbers."""

    block: str
    heights: list[np.ndarray]  # W arrays, entry w - 1 of shape (P 2^w,)
    codes: np.ndarray  # (P 2^W,)
    base: int
    transient: int
    mods: int
    values: int


def successors(block: str, width: int) -> np.ndarray:
    """The two moves of every node of the width-`width` game, node phase * 2^width + cells, free cell 0 then 1."""
    source, target = game.moves(block, width)  # (2 P n,), (2 P n,)
    nodes = len(block) << width
    out = np.empty((2, nodes), dtype=np.int64)  # (2, P n)
    free = np.repeat(np.arange(2 * len(block)) % 2, 1 << width)  # (2 P n,), the free cell of each move
    out[free, source] = target
    return out


def levels(block: str, width: int) -> list[np.ndarray]:
    """The heights of `Certificate.heights`: entry w - 1 is -1 off Q_w, 0 on Z_w and the longest walk to Z_w on the
    rest of Q_w, for w = 1 .. `width`."""
    period = len(block)
    out: list[np.ndarray] = []
    for w in range(1, width + 1):
        nodes = period << w
        succ = successors(block, w)  # (2, P 2^w)
        index = np.arange(nodes)  # (P 2^w,)
        if out:
            prefix = ((index >> w) << (w - 1)) | (index & ((1 << (w - 1)) - 1))  # (P 2^w,)
            inside = out[-1][prefix] == 0  # (P 2^w,), Q_w
        else:
            inside = np.ones(nodes, dtype=bool)  # (P 2^w,)
        settled = inside.copy()  # (P 2^w,)
        while True:
            image = np.zeros(nodes, dtype=bool)  # (P 2^w,)
            image[succ[:, settled].ravel()] = True
            if (image == settled).all():
                break
            settled = image
        height = np.full(nodes, -1, dtype=np.int64)  # (P 2^w,)
        height[settled] = 0
        pending = inside & ~settled  # (P 2^w,)
        while pending.any():
            known = (height[succ[0]] >= 0) & (height[succ[1]] >= 0) & pending  # (P 2^w,)
            if not known.any():
                raise ValueError(f"{block} at width {w}: a cycle off the settled set")
            height[known] = 1 + np.maximum(height[succ[0, known]], height[succ[1, known]])
            pending &= ~known
        out.append(height)
    return out


def final_labels(block: str, width: int, zero: np.ndarray) -> tuple[np.ndarray, int, int, int, int]:
    """On the nodes where `zero` (shape (P 2^width,)) holds, a set closed under moves: each node's code rank * base +
    label (-1 elsewhere), base, and the transient ranks, the moduli and the values packed as in `Certificate`. Raises
    ValueError when the left column is not a function of the cyclic class in some component that can hold a play."""
    period, nodes = len(block), len(block) << width
    succ = successors(block, width)  # (2, P 2^width)
    members = np.flatnonzero(zero)  # (m,)
    local = np.full(nodes, -1, dtype=np.int64)  # (P 2^width,)
    local[members] = np.arange(members.size)
    src = np.tile(np.arange(members.size), 2)  # (2 m,)
    tgt = local[succ[:, members].ravel()]  # (2 m,)
    if (tgt < 0).any():
        raise ValueError(f"{block} at width {width}: the set is not closed under moves")
    graph = csr_matrix((np.ones(src.size, dtype=np.int8), (src, tgt)), shape=(members.size, members.size))
    count, label = connected_components(graph, directed=True, connection="strong")  # (m,)
    inside = label[src] == label[tgt]  # (2 m,)
    recurrent = np.zeros(count, dtype=bool)  # (components,)
    recurrent[label[src[inside]]] = True
    predecessors: dict[int, set[int]] = {c: set() for c in range(count)}
    for a, b in zip(label[src[~inside]].tolist(), label[tgt[~inside]].tolist(), strict=True):
        predecessors[b].add(a)
    layer: dict[int, int] = {}
    order = list(TopologicalSorter(predecessors).static_order())
    for component in order:
        layer[component] = max((layer[p] + 1 for p in predecessors[component]), default=0)
    place = {component: i + 1 for i, component in enumerate(c for c in order if recurrent[c])}
    stride = len(place) + 1
    rank_of = np.array([layer[c] * stride + place.get(c, 0) for c in range(count)])  # (components,)
    phase_of = members >> width  # (m,)
    cells = members & ((1 << width) - 1)  # (m,)
    c = np.array([int(ch) for ch in block], dtype=np.int64)  # (P,)
    reading = c[(phase_of + 1) % period] ^ (c[phase_of] | (cells & 1))  # (m,), the left column
    inner = csr_matrix((np.ones(int(inside.sum()), dtype=np.int8), (src[inside], tgt[inside])),
                       shape=(members.size, members.size))
    level = np.zeros(members.size, dtype=np.int64)  # (m,)
    labels = np.zeros(members.size, dtype=np.int64)  # (m,)
    mods: dict[int, int] = {}
    for component in np.flatnonzero(recurrent).tolist():
        nodes_c = np.flatnonzero(label == component)  # (k,)
        order_c, parent = breadth_first_order(inner, int(nodes_c[0]), directed=True, return_predecessors=True)
        for v in order_c[1:].tolist():
            level[v] = level[parent[v]] + 1
        moves_c = inside & (label[src] == component)  # (2 m,)
        cycle = 0
        for gap in np.unique(np.abs(level[src[moves_c]] + 1 - level[tgt[moves_c]])).tolist():
            cycle = math.gcd(cycle, int(gap))
        labels[nodes_c] = level[nodes_c] % cycle
        seen = np.zeros((cycle, 2), dtype=bool)  # (d, 2)
        seen[labels[nodes_c], reading[nodes_c]] = True
        if seen.all(axis=1).any():
            raise ValueError(f"{block} at width {width}: the left column is not a function of the class")
        mods[int(rank_of[component])] = cycle
    base = max(mods.values())
    rank = rank_of[label]  # (m,)
    codes = np.full(nodes, -1, dtype=np.int64)  # (P 2^width,)
    codes[members] = rank * base + labels
    transient = sum(1 << int(r) for r in np.unique(rank[~recurrent[label]]).tolist())
    packed_mods = sum(d << (8 * r) for r, d in mods.items())
    keep = recurrent[label]  # (m,)
    values = sum(1 << int(i) for i in np.unique((rank * base + labels)[keep & (reading == 1)]).tolist())
    return codes, base, transient, packed_mods, values


def certificate(block: str, width: int) -> Certificate:
    """The whole certificate for `block` at `width`."""
    heights = levels(block, width)
    codes, base, transient, mods, values = final_labels(block, width, heights[-1] == 0)
    return Certificate(block, heights, codes, base, transient, mods, values)


@functools.lru_cache(maxsize=1 << 18)
def step(block: str, width: int, phase: int, cells: int, free: int) -> tuple[int, int]:
    """One move written cell by cell, for `check`: the next phase and cells. `check` asks each move of the widest level
    twice, and a check of a second certificate of the same block asks them all again, so the moves are kept."""
    row = [int(block[phase])] + [(cells >> i) & 1 for i in range(width)] + [free]
    new = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, width + 1)]
    return (phase + 1) % len(block), sum(bit << i for i, bit in enumerate(new))


def check(cert: Certificate) -> bool:
    """The conditions of `ClassCert.levelOk` and `ClassCert.finalOk`, node by node with `step`."""
    block, period = cert.block, len(cert.block)
    width = len(cert.heights)
    for w in range(1, width + 1):
        here = cert.heights[w - 1]
        for phase in range(period):
            for prefix in range(1 << (w - 1)):
                previous = 0 if w == 1 else int(cert.heights[w - 2][(phase << (w - 1)) + prefix])
                if previous != 0:
                    continue
                for top in (0, 1):
                    x = prefix + (top << (w - 1))
                    a = int(here[(phase << w) + x])
                    if a < 0:
                        return False
                    for free in (0, 1):
                        nphase, y = step(block, w, phase, x, free)
                        b = int(here[(nphase << w) + y])
                        if b < 0 or (a == 0 and b != 0) or (a > 0 and b >= a):
                            return False
    last = cert.heights[-1]
    c = [int(ch) for ch in block]
    for phase in range(period):
        for x in range(1 << width):
            if last[(phase << width) + x] != 0:
                continue
            v = int(cert.codes[(phase << width) + x])
            rank, label = divmod(v, cert.base)
            for free in (0, 1):
                nphase, y = step(block, width, phase, x, free)
                v2 = int(cert.codes[(nphase << width) + y])
                if v < 0 or v2 < 0:
                    return False
                rank2, label2 = divmod(v2, cert.base)
                if (cert.transient >> rank) & 1:
                    if not rank < rank2:
                        return False
                else:
                    mod = (cert.mods >> (8 * rank)) & 255
                    if mod == 0 or rank2 < rank or (rank2 == rank and label2 != (label + 1) % mod):
                        return False
            if not (cert.transient >> rank) & 1:
                reading = c[(phase + 1) % period] ^ (c[phase] | (x & 1))
                if (cert.values >> (rank * cert.base + label)) & 1 != reading:
                    return False
    return True


def trie(items: list[tuple[int, int]]) -> str:
    """The Lean `KeyTrie` of (key, value) pairs with distinct keys: `te` empty, `ts key value` one entry, `tn l r` the
    entries of even keys (halved) on the left and of odd keys on the right."""
    if not items:
        return "te"
    if len(items) == 1:
        return f"(ts {items[0][0]} {items[0][1]})"
    even = [(k >> 1, v) for k, v in items if k & 1 == 0]
    odd = [(k >> 1, v) for k, v in items if k & 1]
    return f"(tn {trie(even)} {trie(odd)})"


def phase_tries(table: np.ndarray, period: int, width: int) -> list[str]:
    """One trie per phase of the entries of `table` (shape (P 2^width,)) that are not -1."""
    out = []
    for phase in range(period):
        row = table[phase << width:(phase + 1) << width]  # (2^width,)
        keys = np.flatnonzero(row >= 0)  # (k,)
        out.append(trie(list(zip(keys.tolist(), row[keys].tolist(), strict=True))))
    return out


def lean_data(cert: Certificate, name: str) -> str:
    """The Lean definitions of the certificate: `<name>L<w>` for each width, `<name>F` for the classes and `<name>`,
    the `ClassCert`."""
    period, width = len(cert.block), len(cert.heights)
    out = []
    tables = [(f"{name}L{w}", cert.heights[w - 1], w) for w in range(1, width + 1)] + [(f"{name}F", cert.codes, width)]
    for ident, table, w in tqdm(tables, desc="tries", file=sys.stderr):
        body = ",\n  ".join(phase_tries(table, period, w))
        out.append(f"open KeyTrie in\ndef {ident} : List KeyTrie := [\n  {body}]\n")
    names = ", ".join(f"{name}L{w}" for w in range(1, width + 1))
    out.append(f"def {name} : ClassCert where\n  block := wordOf {period} 0b{cert.block}\n  levels := [{names}]\n"
               f"  final := {name}F\n  base := {cert.base}\n  transient := 0x{cert.transient:x}\n"
               f"  mods := 0x{cert.mods:x}\n  values := 0x{cert.values:x}\n")
    return "\n".join(out)


def lean_checks(name: str, period: int, width: int) -> str:
    """One kernel check per width and phase (`levelOk`) and per phase of the classes (`finalOk`), each in its own
    declaration so that the kernel holds the tables of one at a time, and the theorem `<name>_valid` that gathers
    them."""
    out = []
    for j in range(width):
        for phase in range(period):
            statement = f"{name}.levelOk {j} {phase} = true"
            out.append(f"set_option maxHeartbeats 0 in\ntheorem {name}_l{j}_{phase} : {statement} := by\n"
                       "  decide +kernel\n")
        cases = "".join(f"  | {phase}, _ => {name}_l{j}_{phase}\n" for phase in range(period))
        out.append(f"theorem {name}_l{j} : ∀ φ, φ < {period} → {name}.levelOk {j} φ = true\n{cases}"
                   f"  | _ + {period}, h => absurd h (by omega)\n")
    for phase in range(period):
        out.append(f"set_option maxHeartbeats 0 in\ntheorem {name}_f{phase} : {name}.finalOk {phase} = true := by\n"
                   f"  decide +kernel\n")
    cases = "".join(f"  | {phase}, _ => {name}_f{phase}\n" for phase in range(period))
    out.append(f"theorem {name}_f : ∀ φ, φ < {period} → {name}.finalOk φ = true\n{cases}"
               f"  | _ + {period}, h => absurd h (by omega)\n")
    cases = "".join(f"  | {j}, _ => {name}_l{j}\n" for j in range(width))
    out.append(f"theorem {name}_levels : ∀ j, j < {width} → ∀ φ, φ < {period} → {name}.levelOk j φ = true\n"
               f"{cases}  | _ + {width}, h => absurd h (by omega)\n")
    out.append(f"/-- The certificate passes at every width and phase. -/\ntheorem {name}_valid : {name}.Valid := by\n"
               f"  have hP : {name}.block.length = {period} := Rule30StripCertificateTable.wordOf_length _ _\n"
               f"  have hW : {name}.levels.length = {width} := rfl\n"
               f"  exact ⟨by omega, by omega, fun j φ hj hφ => {name}_levels j (by omega) φ (by omega),\n"
               f"    fun φ hφ => {name}_f φ (by omega)⟩\n")
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--block", default="000000001011")
    parser.add_argument("--width", type=int, default=16)
    parser.add_argument("--lean", action="store_true", help="print the certificate as Lean definitions")
    parser.add_argument("--check", action="store_true", help="also re-run the conditions node by node")
    args = parser.parse_args()
    cert = certificate(args.block, args.width)
    if args.lean:
        name = f"cls{args.block}"
        print(lean_data(cert, name))
        print(lean_checks(name, len(args.block), args.width))
        return
    for w, height in enumerate(cert.heights, start=1):
        print(f"width {w}: {int((height >= 0).sum())} nodes checked, {int((height == 0).sum())} settled, "
              f"heights up to {int(height.max())}")
    print(f"widths: {sum(int((height >= 0).sum()) for height in cert.heights)} nodes checked in all")
    codes = cert.codes[cert.codes >= 0]  # (m,)
    print(f"classes on {codes.size} nodes: ranks up to {int(codes.max()) // cert.base}, base {cert.base}")
    if args.check:
        print(f"check: {check(cert)}")


if __name__ == "__main__":
    main()
