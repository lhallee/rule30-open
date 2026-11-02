"""Lower bounds on the least certificate m(t) of the center cell: combs, maximal monomials, windows, and m(16).

c_t is the center after t steps of Rule 30 as a Boolean function of the 2t + 1 cells x_{-t} .. x_t of a row (bit i of
a row index is x_{-t+i}), and m(t) is the least number of fixed cells of a subcube (a partial row) on which c_t is
constant (`min_certificate`). This module computes the quantities of the entry CertificateLower:

* `comb_cells` and `comb_derivative`: the comb B_j(t) = {-t+1, -t+3, ..., -t+2j+1, -t+2j+2} and the values of the
  mixed derivative of c_t over it (the xor of c_t over the 2^(j+2) rows obtained by flipping cells of the comb). The
  Lean module proves that this derivative is the constant C(t, j+1) mod 2 on every row.
* `maximal_monomials` and `hitting_number`: the monomials of the algebraic normal form of c_t that lie in no other
  monomial, and the least number of cells that meet all of them. A subcube on which c_t is constant fixes a cell of
  every maximal monomial, so the hitting number is a lower bound on m(t); it is at most 3 for t <= 11.
* `window_lengths`: W(t, k), the least length L such that no assignment of the cells outside the window
  x_{-t+k} .. x_{-t+k+L-1} makes c_t constant on the window. Every constant subcube fixes a cell in each such window,
  so `window_bound`, one plus the most pairwise disjoint such windows, is a lower bound on m(t).
* `no_small_subcube`: whether no subcube with at most `cap` fixed cells makes g constant, g being c_t with x_{-t}
  white (`min_certificate.least_constant_subcube` with split_left). It is the breadth-first pass of
  `min_certificate.shortest_implicant` with a cap, run separately below each partial subcube of the `split` rightmost
  cells, which keeps the memory under 4 GB at t = 16. With cap = t - 3 it checks m(t) >= t - 1.

* `screened_functions`, `right_free_least`: the least subcubes among those that leave x_{r+1} .. x_t free, from the
  functions of x_{-t+1} .. x_r that say where c_t is 1 (or 0) for every value of the free cells; the rows are built in
  chunks, so this runs at t = 17 and 18, where the whole table does not fit in 4 GB.
* `absorption_times`: a sampled heuristic for the times at which the cells beside the wall of a long stripe settle.
* `subcube_values`, `far_stripe_values`: c_t over every completion of a partial row, and over every completion of
  the far stripe of StripeGrowth (x_{-i} = (i odd) for 2k + 1 <= i <= t), which the Lean module proves constant for
  t >= 9(k + 1).

    python -m computations.certificate_lower --comb-t 9 --monomial-t 11 --window-t 14 --check-t 16 --cap 11 --split 8 \
        --free 16:1,17:1,18:2 --stripe 16:1,17:1,18:1,19:1 --absorption
"""

from __future__ import annotations

import argparse
import itertools
import sys
from math import comb

import numpy as np

from tqdm.auto import tqdm

from computations.min_certificate import RULES, as_integer, packed_table, unpacked_table
from computations.query_depth import inner_slices


def comb_cells(t: int, j: int) -> list[int]:
    """The comb B_j(t): the cells -t + 1 + 2i for 0 <= i <= j and the cell -t + 2j + 2."""
    return [-t + 1 + 2 * i for i in range(j + 1)] + [-t + 2 * j + 2]


def mixed_derivative(table: np.ndarray, t: int, cells: list[int]) -> np.ndarray:
    """The xor of c_t over the flips of the given cone cells, at every row: entry i is the derivative at the row i."""
    # table: (2^(2t+1),) uint8, entry i is c_t at the row with index i
    out = table.copy()  # (2^(2t+1),)
    for cell in cells:
        bit = cell + t
        view = out.reshape(-1, 2, 1 << bit)  # (high cells, x_cell, low cells)
        out = (view ^ view[:, ::-1, :]).reshape(-1)  # (2^(2t+1),)
    return out


def comb_derivative(t: int, j: int) -> set[int]:
    """The values that the mixed derivative of c_t over the comb B_j(t) takes on the rows of the cone."""
    cells = comb_cells(t, j)
    if cells[-1] > t:
        raise ValueError("the comb leaves the cone")
    return set(mixed_derivative(unpacked_table(t), t, cells).tolist())


def anf(table: np.ndarray, n: int) -> np.ndarray:
    """The coefficients of the algebraic normal form (the Moebius transform over GF(2)): entry S is the coefficient of
    the monomial on the cells of the bits of S."""
    # table: (2^n,) uint8
    out = table.astype(np.uint8)  # (2^n,), a copy
    for i in range(n):
        view = out.reshape(-1, 2, 1 << i)  # (high, bit i, low)
        view[:, 1, :] ^= view[:, 0, :]
    return out


def maximal_monomials(t: int) -> list[int]:
    """The nonconstant monomials of the algebraic normal form of c_t contained in no other monomial, as bit masks."""
    n = 2 * t + 1
    present = anf(unpacked_table(t), n).astype(bool)  # (2^n,)
    present[0] = False
    above = present.copy()  # (2^n,), entry S: some monomial contains S
    for i in range(n):
        view = above.reshape(-1, 2, 1 << i)
        view[:, 0, :] |= view[:, 1, :]
    masks = np.nonzero(present)[0]  # (number of monomials,)
    strict = np.zeros(len(masks), dtype=bool)  # (number of monomials,)
    for i in range(n):
        strict |= (((masks >> i) & 1) == 0) & above[masks | (1 << i)]
    return [int(m) for m in masks[~strict]]


def hitting_number(t: int, most: int = 4) -> tuple[int | None, list[int]]:
    """(least number of cells meeting every maximal monomial of c_t, one such set of cells), searching sets of at
    most `most` cells; (None, []) if none is that small."""
    n = 2 * t + 1
    maximal = maximal_monomials(t)
    for size in range(1, most + 1):
        for cells in itertools.combinations(range(n), size):
            mask = sum(1 << i for i in cells)
            if all(m & mask for m in maximal):
                return size, [i - t for i in cells]
    return None, []


def window_lengths(t: int, longest: int = 9, table: np.ndarray | None = None) -> list[int | None]:
    """W(t, k) for k = 1 .. 2t: the least L <= `longest` such that for every assignment of the cells outside the
    window x_{-t+k} .. x_{-t+k+L-1}, c_t takes both values on the window; None if there is none within the cone."""
    n = 2 * t  # g = c_t with x_{-t} white; c_t = x_{-t} xor g, so windows right of x_{-t} see g
    g = unpacked_table(t, white_left=True) if table is None else table  # (2^(2t),), bit k-1 is x_{-t+k}
    out: list[int | None] = []
    for k in range(1, n + 1):
        found = None
        for length in range(1, min(longest, n - k + 1) + 1):
            view = g.reshape(1 << (n - k + 1 - length), 1 << length, 1 << (k - 1))  # (right, window, left)
            if not bool((view.min(axis=1) == view.max(axis=1)).any()):
                found = length
                break
        out.append(found)
    return out


def window_bound(lengths: list[int | None]) -> int:
    """One (for x_{-t}) plus the most pairwise disjoint windows [k, k + W(t, k)), each of which every constant subcube
    meets: the greedy choice by earliest end is optimal for intervals."""
    ends = sorted((k + w - 1, k) for k, w in enumerate(lengths, 1) if w is not None)
    count, last = 0, 0
    for end, start in ends:
        if start > last:
            count, last = count + 1, end
    return 1 + count


def capped_pass(start: dict[int, int], n: int, first: int, cap: int) -> bool:
    """Whether some completion of the partial subcubes in `start` (state -> cost after the cells n - 1 .. n - first)
    reaches a subcube of the n variables with at most `cap` fixed cells on which the function is 1."""
    level = start
    for j in range(first, n):
        half = 1 << (n - j - 1)
        mask = (1 << half) - 1
        new: dict[int, int] = {}  # state -> least cost
        for state, cost in level.items():
            low, high = state & mask, state >> half
            for nxt, c in ((low & high, cost), (low, cost + 1), (high, cost + 1)):
                if c > cap or nxt == 0:
                    continue
                if nxt == mask:
                    return True
                old = new.get(nxt)
                if old is None or c < old:
                    new[nxt] = c
        level = new
    return False


def no_small_subcube(t: int, cap: int, split: int = 6, progress: bool = True) -> bool:
    """True if no subcube with at most `cap` fixed cells among x_{-t+1} .. x_t makes g = c_t(x_{-t} = 0) constant,
    so that m(t) >= cap + 2 (every constant subcube of c_t also fixes x_{-t}). The cells are read from the right; the
    partial subcubes of the `split` rightmost cells are listed, and the pass runs below each of them in turn."""
    n = 2 * t
    full = (1 << (1 << n)) - 1
    for complement in (False, True):
        table = packed_table(t, white_left=True)  # built again for the complement, so that it can be dropped
        level: dict[int, int] = {table ^ full if complement else table: 0}  # state -> least cost
        del table
        for j in range(split):
            half = 1 << (n - j - 1)
            mask = (1 << half) - 1
            new: dict[int, int] = {}
            for state, cost in level.items():
                low, high = state & mask, state >> half
                for nxt, c in ((low & high, cost), (low, cost + 1), (high, cost + 1)):
                    if c > cap or nxt == 0:
                        continue
                    if nxt == mask:
                        return False
                    if nxt not in new or c < new[nxt]:
                        new[nxt] = c
            level = new
        items: list = sorted(level.items(), key=lambda item: item[1])  # (state, cost), freed as the pass goes
        del level
        for i in tqdm(range(len(items)), desc=f"t={t} below {split} cells", file=sys.stderr, disable=not progress):
            state, cost = items[i]
            items[i] = None
            if capped_pass({state: cost}, n, split, cap):
                return False
            del state
    return True


def screened_functions(t: int, r: int, inner: int = 22, progress: bool = True) -> tuple[int, int]:
    """(A, B) as functions of the t + r cells x_{-t+1} .. x_r (bit j is x_{-t+1+j}), with x_{-t} white: A is 1 where
    g = c_t is 1 for every value of the free cells x_{r+1} .. x_t, B where it is 0 for every value. The rows are
    bit-sliced on the `inner` lowest cells and the other cells, all free, are fixed in an outer loop, so the memory is
    about 2t 2^(inner - 3) bytes whatever t is."""
    n = 2 * t
    left = t + r
    m = min(max(inner, left), n)
    if left < 6:
        raise ValueError("t + r must be at least 6")
    step = RULES[30]
    slices = inner_slices(m)  # m x (2^(m-6),) uint64
    ones = np.full(1 << (m - 6), 0xFFFFFFFFFFFFFFFF, dtype=np.uint64)  # (2^(m-6),), AND of the chunks
    any_one = np.zeros(1 << (m - 6), dtype=np.uint64)  # (2^(m-6),), OR of the chunks
    for a in tqdm(range(1 << (n - m)), desc=f"screen t={t} r={r}", file=sys.stderr, disable=not progress):
        outer = [np.uint64(0xFFFFFFFFFFFFFFFF) if (a >> i) & 1 else np.uint64(0) for i in range(n - m)]
        words: list = [np.uint64(0)] + slices + outer  # 2t + 1 cells: arrays (2^(m-6),) or uint64 scalars
        for _ in range(t):
            words = [step(words[i - 1], words[i], words[i + 1]) for i in range(1, len(words) - 1)]
        center = np.broadcast_to(words[0], ones.shape)  # (2^(m-6),)
        ones &= center
        any_one |= center
    # the inner cells left .. m - 1 are free too: fold them, they are the high bits of the word index
    ones = np.bitwise_and.reduce(ones.reshape(1 << (m - left), 1 << (left - 6)), axis=0)  # (2^(left-6),)
    any_one = np.bitwise_or.reduce(any_one.reshape(1 << (m - left), 1 << (left - 6)), axis=0)  # (2^(left-6),)
    to_int = lambda words: int.from_bytes(words.astype("<u8").tobytes(), "little")  # noqa: E731
    return to_int(ones), to_int(~any_one)


def least_listing(h: int, n: int, limit: int = 50) -> tuple[int | None, list[str]]:
    """(least number of fixed cells of a subcube of the n variables on which h is 1, the least subcubes as strings
    over 0, 1 and * from variable 0 to variable n - 1, at most `limit` per state): the pass of
    `min_certificate.least_subcubes` on one function."""
    if h == 0:
        return None, []
    level: dict[int, tuple[int, list[str]]] = {h: (0, [""])}  # state -> (cost, partial subcubes read from the top)
    best, out = n + 1, []
    for j in range(n):
        half = 1 << (n - j - 1)
        mask = (1 << half) - 1
        new: dict[int, tuple[int, list[str]]] = {}
        for state, (cost, partials) in level.items():
            low, high = state & mask, state >> half
            for nxt, c, mark in ((low & high, cost, "*"), (low, cost + 1, "0"), (high, cost + 1, "1")):
                if nxt == 0 or c > best:
                    continue
                grown = [p + mark for p in partials]
                if nxt == mask:
                    if c < best:
                        best, out = c, []
                    out += [(p + "*" * (n - j - 1))[::-1] for p in grown]
                    continue
                if c == best:
                    continue
                old = new.get(nxt)
                if old is None or c < old[0]:
                    new[nxt] = (c, grown[:limit])
                elif c == old[0]:
                    new[nxt] = (c, (old[1] + grown)[:limit])
        level = new
    return best, out


def right_free_least(t: int, r: int, inner: int = 22, progress: bool = True) -> tuple[int | None, list[str]]:
    """(least number of fixed cells, x_{-t} included, of a subcube with x_{r+1} .. x_t free on which c_t is constant;
    the least subcubes with x_{-t} = 0 as strings x_{-t} .. x_t). An upper bound on m(t), equal to it when some least
    subcube leaves those cells free."""
    ones, zeros = screened_functions(t, r, inner, progress)
    found = [least_listing(h, t + r) for h in (ones, zeros)]
    sizes = [size for size, _ in found if size is not None]
    if not sizes:
        return None, []
    least = min(sizes)
    rows = ["0" + row + "*" * (t - r) for size, rows in found if size == least for row in rows]
    return least + 1, rows


def subcube_values(t: int, partial: str) -> set[int]:
    """The values of c_t over every completion of a partial row, given as a string x_{-t} .. x_t over 0, 1 and *
    (2^(number of *) rows, bit-sliced)."""
    free = [i for i, ch in enumerate(partial) if ch == "*"]
    rows = 1 << len(free)
    index = np.arange(rows, dtype=np.uint64)  # (rows,)
    cells = []  # 2t + 1 packed rows, each (max(1, rows / 8),) uint8
    for i, ch in enumerate(partial):
        if ch == "*":
            bits = ((index >> np.uint64(free.index(i))) & np.uint64(1)).astype(np.uint8)  # (rows,)
            cells.append(np.packbits(bits, bitorder="little"))
        else:
            cells.append(np.full(max(1, rows // 8), 0xFF if ch == "1" else 0, dtype=np.uint8))
    for _ in range(t):
        cells = [cells[i - 1] ^ (cells[i] | cells[i + 1]) for i in range(1, len(cells) - 1)]
    return set(np.unpackbits(cells[0], bitorder="little")[:rows].tolist())


def far_stripe_values(t: int, k: int) -> set[int]:
    """The values of c_t over every row with x_{-i} = (i odd) for 2k + 1 <= i <= t and every other cone cell free:
    {0} when the far stripe of StripeGrowth fixes the center."""
    partial = "".join(str((t - i) % 2) if t - i >= 2 * k + 1 else "*" for i in range(2 * t + 1))  # x_{-t} .. x_t
    return subcube_values(t, partial)


def absorption_times(length: int = 90, steps: int = 80, samples: int = 20000, cells: int = 16,
                     seed: int = 2) -> list[int | None]:
    """A sampled heuristic, not a proof: with the odd stripe on -1 .. -length and random cells right of the wall, the
    first time from which the cell d (d = 0 .. cells - 1) takes one value in every sample up to steps - 10."""
    rng = np.random.default_rng(seed)
    width = 2 * length + steps + 2
    row = rng.integers(0, 2, size=(samples, width), dtype=np.uint8)  # (samples, width), cell 0 at index length
    for j in range(1, length + 1):
        row[:, length - j] = j % 2
    seen = []
    for _ in range(steps + 1):
        seen.append(row[:, length: length + cells].copy())  # (samples, cells)
        inner = row[:, :-2] ^ (row[:, 1:-1] | row[:, 2:])  # (samples, width - 2)
        row = np.concatenate([np.zeros((samples, 1), np.uint8), inner, np.zeros((samples, 1), np.uint8)], axis=1)
    history = np.stack(seen)  # (steps + 1, samples, cells)
    constant = history.min(axis=1) == history.max(axis=1)  # (steps + 1, cells)
    out: list[int | None] = []
    for d in range(cells):
        out.append(next((s for s in range(steps - 9) if constant[s: steps - 9, d].all()), None))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--comb-t", type=int, default=9, help="check the comb derivatives for t <= this")
    parser.add_argument("--monomial-t", type=int, default=11, help="maximal monomials for t <= this")
    parser.add_argument("--window-t", type=int, default=12, help="window lengths for t <= this")
    parser.add_argument("--check-t", type=int, default=0, help="check m(t) >= t - 1 at this t (0: skip)")
    parser.add_argument("--cap", type=int, default=None, help="with --check-t: the cap on g (default t - 3)")
    parser.add_argument("--free", type=str, default="", help="t:r pairs, the least subcubes with x_{r+1} .. x_t free")
    parser.add_argument("--stripe", type=str, default="18:1", help="t:k pairs, the far stripe over every completion")
    parser.add_argument("--absorption", action="store_true", help="sample the absorption times beside the wall")
    parser.add_argument("--split", type=int, default=6, help="cells listed before the pass in the check")
    args = parser.parse_args()

    print("t  j  comb B_j(t)  values of the mixed derivative  C(t, j+1) mod 2")
    for t in range(1, args.comb_t + 1):
        for j in range(t):
            if comb_cells(t, j)[-1] > t:
                break
            print(t, j, comb_cells(t, j), sorted(comb_derivative(t, j)), comb(t, j + 1) % 2, flush=True)
    print("t  maximal monomials  hitting number  a hitting set")
    for t in tqdm(range(1, args.monomial_t + 1), desc="monomials", file=sys.stderr):
        print(t, len(maximal_monomials(t)), *hitting_number(t), flush=True)
    print("t  W(t, k) for k = 1 .. 2t  window bound  t - 1")
    for t in tqdm(range(1, args.window_t + 1), desc="windows", file=sys.stderr):
        lengths = window_lengths(t)
        print(t, lengths, window_bound(lengths), t - 1, flush=True)
    if args.check_t:
        t = args.check_t
        cap = t - 3 if args.cap is None else args.cap
        print(t, f"no subcube with at most {cap + 1} fixed cells makes c_t constant:",
              no_small_subcube(t, cap, args.split), flush=True)
    print("t  r  least fixed cells with x_{r+1} .. x_t free  least subcubes with x_{-t} = 0 (x_{-t} .. x_t)")
    for pair in filter(None, args.free.split(",")):
        t, r = map(int, pair.split(":"))
        least, rows = right_free_least(t, r)
        print(t, r, least, flush=True)
        for row in rows[:10]:
            print("   ", row, "values of c_t over every completion:", sorted(subcube_values(t, row)), flush=True)
    print("t  k  fixed cells t - 2k  values of c_t on the far stripe")
    for pair in filter(None, args.stripe.split(",")):
        t, k = map(int, pair.split(":"))
        print(t, k, t - 2 * k, sorted(far_stripe_values(t, k)), flush=True)
    if args.absorption:
        print("sampled: first time from which cell d beside the wall at -1 is fixed, d = 0 ..", absorption_times())


if __name__ == "__main__":
    main()
