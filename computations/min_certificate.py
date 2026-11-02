"""The least certificate of the center cell over all rows: the fewest cells of a partial row that make c_t constant.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of row 0 (Rule 30: new x_j = x_{j-1} xor (x_j or
x_{j+1})); bit i of a row index is x_{-t+i}. A subcube is a partial row: each cell fixed to 0, fixed to 1, or free.
m(t) is the least number of fixed cells of a subcube on which c_t is constant: the length of the shortest prime
implicant of c_t or of its complement, or the smallest certificate of the best row (the best case of a decision tree:
its shallowest leaf).

* `shortest_implicant` finds the least number of fixed cells of a subcube on which a function is 1, exactly, by a
  breadth-first pass that reads the cells from the right, x_t first. The state after the r rightmost cells is the
  function of the other cells that is 1 where every completion inside the partial subcube is 1: fixing the cell to b
  keeps the half b, leaving it free keeps the AND of the two halves. Equal states have equal futures, so one state
  keeps its least cost, and the pass is exhaustive over all 3^n subcubes. It also counts the subcubes of least size.
  With `right_determined=True` a cell is not fixed to a constant but chosen as a function of the cells read after it
  (the OR of the halves), and `routing` reads the cells from the left for it, so that each chosen cell is a function
  of the cells to its right: this class of sets is mapped into itself by one step of the rule.
* `least_constant_subcube` is m(t) for Rules 30, 90 and 150 from the packed truth table of c_t (from t = 12 on,
  `main` searches the half table with x_{-t} = 0, which every constant subcube fixes), and
  `ternary_minimum` the same number from the dynamic program over the 3^(2t+1) subcubes of
  `query_certificates.subcube_constant`, used as a check for t <= 8.
* `routing` is the quantity behind the proof plan: for the leftmost free cell u = -t + k of a subcube, R(t, k) is the
  least number of fixed cells right of u on a subcube where the derivative D_u c_t (c_t xor c_t with x_u flipped) is
  identically 0, over the 2^k values of the cells left of u. R(t, k) >= t - k - 1 for every k gives m(t) >= t - 1.
* `least_subcubes` lists the subcubes of least size.
* `stripe_values` evaluates c_t on the stripe subcube (x_{-t} fixed, x_{-j} = 1 exactly for even j, 2 <= j <= t - 1,
  and x_{-1} .. x_t free), whose t - 1 fixed cells make c_t constant for t >= 9.

    python -m computations.min_certificate --max-t 15 --controls-t 10 --routing-t 14 --stripe-t 16 --dp-t 8
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Callable

import numpy as np

from tqdm.auto import tqdm

from computations.cone_screening import step_slices, variable_slices
from computations.query_certificates import free_counts, subcube_constant
from computations.query_depth import inner_slices

Step = Callable[[np.ndarray, np.ndarray, np.ndarray], np.ndarray]
RULES: dict[int, Step] = {
    30: lambda left, center, right: left ^ (center | right),
    90: lambda left, center, right: left ^ right,
    150: lambda left, center, right: left ^ center ^ right,
}


def packed_table(t: int, rule: int = 30, inner: int = 24, white_left: bool = False) -> int:
    """The truth table of c_t under the rule as an integer: bit i is c_t at the row whose index is i (bit j of i is
    x_{-t+j}). With white_left, x_{-t} = 0 and the table has the 2t variables x_{-t+1} .. x_t (bit j is x_{-t+1+j}).
    The `inner` lowest variables are bit-sliced on words; the others, the rightmost cells, are fixed in an outer
    loop, one chunk of 2^inner rows at a time, which keeps the memory near 2t 2^(inner - 3) bytes."""
    n = 2 * t + 1 - int(white_left)  # variables
    step = RULES[rule]
    if n < 6:
        row = variable_slices(n)  # n x (2^n,) bools
        if white_left:
            row = [np.zeros(1 << n, dtype=bool)] + row  # (2t + 1) x (2^n,)
        for _ in range(t):
            row = [step(row[i - 1], row[i], row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2) x (2^n,)
        return as_integer(row[0])
    m = min(inner, n)
    slices = inner_slices(m)  # m x (2^(m-6),) uint64, bit b of word w is variable i of assignment 64 w + b
    chunks = []
    for a in range(1 << (n - m)):  # the outer variables m .. n - 1 are the bits of a
        outer = [np.uint64(0xFFFFFFFFFFFFFFFF) if (a >> i) & 1 else np.uint64(0) for i in range(n - m)]
        words: list = [np.uint64(0)] * int(white_left) + slices + outer  # 2t + 1 cells: arrays or uint64 scalars
        for _ in range(t):
            words = [step(words[i - 1], words[i], words[i + 1]) for i in range(1, len(words) - 1)]  # len - 2
        chunks.append(np.broadcast_to(words[0], slices[0].shape).astype("<u8").tobytes())
    return int.from_bytes(b"".join(chunks), "little")


def as_integer(bits: np.ndarray) -> int:
    """A truth table (entry i is the value at index i) as an integer with bit i set where the entry is 1."""
    # bits: (2^n,)
    return int.from_bytes(np.packbits(bits.astype(np.uint8), bitorder="little").tobytes(), "little")


def shortest_implicant(h: int, n: int, cap: int | None = None,
                       right_determined: bool = False) -> tuple[int | None, int]:
    """(least number of fixed cells of a subcube of the n variables on which the function h is 1, number of such
    subcubes). Bit i of h is the value at the index i; variable n - 1 is read first. Only sizes up to `cap` are
    searched; (None, 0) means none. With right_determined, a cell may instead be a function of the cells read after
    it (those of smaller index), and the count is of the cheapest choices of cells, not of functions."""
    full = (1 << (1 << n)) - 1
    if h == full:
        return 0, 1
    best = n + 1 if cap is None else cap + 1
    count = 0
    level: dict[int, tuple[int, int]] = {h: (0, 1)}  # state -> (least cost, number of partial subcubes at that cost)
    for j in range(n):
        half = 1 << (n - j - 1)
        mask = (1 << half) - 1
        new: dict[int, tuple[int, int]] = {}
        for state, (cost, ways) in level.items():
            low, high = state & mask, state >> half
            moves = [(low & high, cost)]
            if right_determined:
                moves.append((low | high, cost + 1))
            else:
                moves += [(low, cost + 1), (high, cost + 1)]
            for nxt, c in moves:
                if c > best or nxt == 0:
                    continue
                if nxt == mask:  # the rest of the cells free
                    if c < best:
                        best, count = c, 0
                    count += ways
                    continue
                if c == best and count == 0:  # best is still the cap, which a completion cannot beat
                    continue
                old = new.get(nxt)
                if old is None or c < old[0]:
                    new[nxt] = (c, ways)
                elif c == old[0]:
                    new[nxt] = (c, old[1] + ways)
        level = new
    if count == 0:
        return None, 0
    return best, count


def least_subcubes(t: int, limit: int = 200) -> list[str]:
    """The subcubes with m(t) fixed cells on which Rule 30's c_t is constant, as strings x_{-t} .. x_t over 0, 1 and *
    (at most `limit` per value of c_t): the pass of `shortest_implicant`, keeping the partial subcubes of each state."""
    n = 2 * t + 1
    least, _ = least_constant_subcube(t)
    table = packed_table(t)
    out = []
    for h in (table, table ^ ((1 << (1 << n)) - 1)):
        level: dict[int, tuple[int, list[str]]] = {h: (0, [""])}  # state -> (cost, partial subcubes read from x_t)
        for j in range(n):
            half = 1 << (n - j - 1)
            mask = (1 << half) - 1
            new: dict[int, tuple[int, list[str]]] = {}
            for state, (cost, partials) in level.items():
                low, high = state & mask, state >> half
                for nxt, c, mark in ((low & high, cost, "*"), (low, cost + 1, "0"), (high, cost + 1, "1")):
                    if c > least or nxt == 0:
                        continue
                    grown = [p + mark for p in partials]
                    if nxt == mask:
                        out += [(p + "*" * (n - j - 1))[::-1] for p in grown]
                        continue
                    if c == least:
                        continue
                    old = new.get(nxt)
                    if old is None or c < old[0]:
                        new[nxt] = (c, grown[:limit])
                    elif c == old[0]:
                        new[nxt] = (c, (old[1] + grown)[:limit])
            level = new
    return out


def least_constant_subcube(t: int, rule: int = 30, cap: int | None = None,
                           split_left: bool = False) -> tuple[int | None, int]:
    """(m(t), number of subcubes with m(t) fixed cells on which c_t is constant) for the rule, searching sizes up
    to `cap`. With split_left the search runs on g = c_t with x_{-t} = 0, a table of half the size: for the three
    rules c_t = x_{-t} xor g, so every constant subcube fixes x_{-t} (Lean `constOn_fixes_left` for Rule 30) and is
    one of the two values of x_{-t} times a subcube on which g is constant."""
    n = 2 * t + 1 - int(split_left)
    table = packed_table(t, rule, white_left=split_left)
    ones, count1 = shortest_implicant(table, n, None if cap is None else cap - int(split_left))
    table ^= (1 << (1 << n)) - 1
    zeros, count0 = shortest_implicant(table, n, None if cap is None else cap - int(split_left))
    del table
    sizes = [s for s in (ones, zeros) if s is not None]
    if not sizes:
        return None, 0
    least = min(sizes)
    count = (count1 if ones == least else 0) + (count0 if zeros == least else 0)
    return (least + 1, 2 * count) if split_left else (least, count)


def unpacked_table(t: int, rule: int = 30, white_left: bool = False) -> np.ndarray:
    """c_t for all 2^(2t+1) rows (2^(2t) with white_left) as a uint8 array, entry i at the row with index i."""
    n = 2 * t + 1 - int(white_left)
    packed = packed_table(t, rule, white_left=white_left).to_bytes(max(1, (1 << n) // 8), "little")
    bits = np.unpackbits(np.frombuffer(packed, dtype=np.uint8), bitorder="little")  # (max(8, 2^n),)
    return bits[: 1 << n]  # (2^n,)


def ternary_minimum(t: int, rule: int = 30) -> tuple[int, int]:
    """(m(t), number of minimum subcubes) by the dynamic program over the 3^(2t+1) subcubes, an independent check
    of `least_constant_subcube`."""
    n = 2 * t + 1
    constant = subcube_constant(unpacked_table(t, rule), n)  # (3,)*n
    free = free_counts(n)[constant]  # (number of constant subcubes,)
    most = int(free.max())
    return n - most, int((free == most).sum())


def routing(t: int, right_determined: bool = False, progress: bool = False) -> list[int]:
    """R(t, k) for k = 1 .. t: the least number of fixed cells right of u = -t + k (each a function of the cells to
    its right, with right_determined) over subcubes with u free and every cell left of u fixed on which D_u c_t is
    identically 0. The cell x_{-t} is held at 0: c_t = x_{-t} xor g with g free of x_{-t} (ConeScreening's
    `center_decomp`), so D_u c_t does not depend on it."""
    n = 2 * t + 1
    g = unpacked_table(t, white_left=True)  # (2^(2t),), the rows with x_{-t} = 0; bit i of the index is x_{-t+1+i}
    out = []
    for k in tqdm(range(1, t + 1), desc=f"routing t={t}", file=sys.stderr, disable=not progress):
        m = n - 1 - k  # cells right of u
        split = g.reshape(1 << m, 2, 1 << (k - 1))  # (2^m, 2, 2^(k-1)): right cells, x_u, x_{-t+1} .. x_{u-1}
        best: int | None = None
        for prefix in range(1 << (k - 1)):
            zero = 1 - (split[:, 0, prefix] ^ split[:, 1, prefix])  # (2^m,), 1 where D_u c_t = 0
            if right_determined:  # x_{u+1} becomes the variable read first, the innermost choice: each chosen cell
                # is then a function of the cells to its right
                zero = zero.reshape((2,) * m).transpose(tuple(range(m - 1, -1, -1))).reshape(-1)  # (2^m,)
            size, _ = shortest_implicant(as_integer(zero), m, None if best is None else best - 1, right_determined)
            if size is not None:
                best = size
        out.append(m + 1 if best is None else best)
    return out


def stripe_values(t: int) -> tuple[np.ndarray, np.ndarray]:
    """c_t on the stripe subcube, for x_{-t} = 0 and x_{-t} = 1: x_{-j} = 1 exactly for even j, 2 <= j <= t - 1,
    and the t + 2 cells x_{-1} .. x_t free (bit i of the index is x_{-1+i})."""
    free = variable_slices(t + 2)  # (t + 2) x (2^(t+2),)
    out = []
    for first in (False, True):
        left = [np.bool_(first)] + [np.bool_(j % 2 == 0) for j in range(t - 1, 1, -1)]  # x_{-t} .. x_{-2}
        center = step_slices(left + list(free), t)[0]  # (2^(t+2),) or a scalar
        out.append(np.broadcast_to(center, (1 << (t + 2),)).astype(np.uint8))  # (2^(t+2),)
    return out[0], out[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-t", type=int, default=12, help="m(t) for Rule 30 for t <= this")
    parser.add_argument("--controls-t", type=int, default=10, help="m(t) for Rules 90 and 150 for t <= this")
    parser.add_argument("--routing-t", type=int, default=10, help="R(t, k) for t <= this")
    parser.add_argument("--stripe-t", type=int, default=16, help="the stripe subcube for 9 <= t <= this")
    parser.add_argument("--dp-t", type=int, default=7, help="check m(t) by the ternary program for t <= this")
    parser.add_argument("--list-t", type=int, default=13, help="list the least subcubes for 9 <= t <= this")
    args = parser.parse_args()

    print("t  m(t) Rule 30  minimum subcubes  t - 1")
    for t in tqdm(range(1, args.max_t + 1), desc="m(t)", file=sys.stderr):
        print(t, *least_constant_subcube(t, split_left=t >= 12), t - 1, flush=True)
    print("t  ternary program: m(t)  minimum subcubes")
    for t in tqdm(range(1, args.dp_t + 1), desc="ternary", file=sys.stderr):
        print(t, *ternary_minimum(t), flush=True)
    print("t  m(t) Rule 90  2^popcount(t)  m(t) Rule 150")
    for t in range(1, args.controls_t + 1):
        print(t, least_constant_subcube(t, 90)[0], 2 ** bin(t).count("1"), least_constant_subcube(t, 150)[0],
              flush=True)
    print("t  R(t, k) for k = 1 .. t  /  R(t, k) - (t - k - 1)  /  right-determined cells")
    for t in range(1, args.routing_t + 1):
        r = routing(t, progress=t >= 11)
        rd = routing(t, right_determined=True, progress=t >= 11)
        print(t, r, [v - (t - k - 1) for k, v in enumerate(r, 1)], rd, flush=True)
    print("t  least subcubes, x_{-t} .. x_t")
    for t in range(9, args.list_t + 1):
        print(t, *least_subcubes(t), flush=True)
    print("t  stripe values (x_{-t} = 0, x_{-t} = 1)")
    for t in range(9, args.stripe_t + 1):
        zero, one = stripe_values(t)
        print(t, sorted(set(zero.tolist())), sorted(set(one.tolist())), flush=True)


if __name__ == "__main__":
    main()
