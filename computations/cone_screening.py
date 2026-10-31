"""The center cell as a function of its cone: an alternating left half screens off the right half.

c_t is a Boolean function of the 2t + 1 cells x_{-t} .. x_t of row 0 (new x_j = x_{j-1} xor (x_j or x_{j+1})). Index
the truth table by the integer whose bit i is x_{-t+i}, so the t lowest bits are the left half x_{-t} .. x_{-1} and the
t + 1 highest bits the right half x_0 .. x_t.

* `pattern_values` fixes the left half to the even pattern (x_{-j} = 1 exactly for even j) or the odd pattern (exactly
  for odd j) and returns c_t for every right half. The values are constant from t = 8 (even, value 1) and t = 9 (odd,
  value 0).
* `pair_step` is the two-cell model behind the argument. Beside a black wall that an alternating stretch ends in, the
  pair (a, b) of the next two cells moves by a' = NOR(a, b), b' = a xor (b or c) with c the third cell, and the
  lemmas `check_pair_lemmas` list (a pair (0, 0) comes from a pair (0, 0) two steps earlier, ...) are checked on every
  case.
* `left_counts` and `right_counts` count the distinct subfunctions of c_t after the k leftmost, or rightmost, cells are
  fixed: the width of every ordered decision diagram, in the order that reads those cells first, at that level.

    python -m computations.cone_screening --max-t 18          # constancy of the two patterns, and the pair lemmas
    python -m computations.cone_screening --counts 10         # subfunction counts for t = 1 .. 10
"""

from __future__ import annotations

import argparse
import itertools
import sys

import numpy as np

from tqdm.auto import tqdm


def step_slices(row: list[np.ndarray | np.bool_], steps: int) -> list[np.ndarray | np.bool_]:
    """Rule 30 on bit-sliced rows: entry i of `row` holds cell i for every assignment at once (an array of bools, or a
    constant). Each step drops the two outermost cells, which have an unknown neighbor."""
    # row: n entries, each (N,) or a scalar
    for _ in range(steps):
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # n - 2 entries
    return row


def variable_slices(count: int) -> list[np.ndarray]:
    """The `count` variables as arrays over all 2^count assignments: entry i is bit i of the assignment index."""
    index = np.arange(1 << count, dtype=np.int64)  # (2^count,)
    return [((index >> i) & 1).astype(bool) for i in range(count)]  # count x (2^count,)


def cone_table(t: int) -> np.ndarray:
    """c_t for all 2^(2t+1) cone assignments; bit i of the index is x_{-t+i}."""
    center = step_slices(variable_slices(2 * t + 1), t)[0]  # (2^(2t+1),)
    return center.astype(np.uint8)  # (2^(2t+1),)


def left_pattern(t: int, odd: bool) -> list[bool]:
    """x_{-t} .. x_{-1} for the pattern with x_{-j} = 1 exactly for the odd j (odd) or the even j (even), 1 <= j <= t."""
    return [(j % 2 == 1) == odd for j in range(t, 0, -1)]  # t entries


def pattern_values(t: int, odd: bool) -> np.ndarray:
    """c_t for the pattern on the left half and every right half x_0 .. x_t; bit i of the index is x_i."""
    right = variable_slices(t + 1)  # (t + 1) x (2^(t+1),)
    row: list[np.ndarray | np.bool_] = [np.bool_(v) for v in left_pattern(t, odd)] + list(right)  # 2t + 1 entries
    center = step_slices(row, t)[0]  # (2^(t+1),)
    return np.broadcast_to(center, (1 << (t + 1),)).astype(np.uint8)  # (2^(t+1),)


def constant_value(values: np.ndarray) -> int | None:
    """0 or 1 when every entry is that bit, else None."""
    # values: (N,)
    if values.all():
        return 1
    if not values.any():
        return 0
    return None


def pair_step(pair: tuple[int, int], third: int) -> tuple[int, int]:
    """One step of the pair (a, b) = (x(s, w+1), x(s, w+2)) beside a black wall at w, with third = x(s, w+3):
    a' = NOR(a, b) and b' = a xor (b or third)."""
    a, b = pair
    return (1 - (a | b), a ^ (b | third))


def check_pair_model(t: int, trials: int, seed: int = 0) -> None:
    """The pair map against a plain run of the rule. A row is an alternating stretch ending in a black wall at cell W
    (black at W, W - 2, ..., white at W - 1, W - 3, ...) and random cells to its right. For t steps the wall and the
    stretch stay as they are, and the pair beside the wall follows `pair_step` with the true third cell."""
    rng = np.random.default_rng(seed)
    for _ in range(trials):
        wall = t + 1 + int(rng.integers(0, 2))
        length = wall + 3 + 2 * t + 2
        row = [int(rng.integers(0, 2)) for _ in range(length)]  # (length,)
        for j in range(wall + 1):
            row[j] = 1 - ((wall - j) % 2)
        first = 0  # the original index of row[0]; each step drops the outermost cell on both sides
        for _ in range(t):
            new = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len(row) - 2,)
            pair = (row[wall + 1 - first], row[wall + 2 - first])
            third = row[wall + 3 - first]
            first += 1
            for j in range(first, wall + 1):
                assert new[j - first] == 1 - ((wall - j) % 2)
            assert (new[wall + 1 - first], new[wall + 2 - first]) == pair_step(pair, third)
            row = new


def check_pair_lemmas() -> dict[str, int]:
    """Every case of the local facts the argument uses, as assertions; returns the number of cases of each."""
    pairs = list(itertools.product((0, 1), repeat=2))  # 4 x (2,)
    counts = {"zero_zero_from_a": 0, "zero_zero_two_back": 0, "b_zero_cases": 0, "seven_eight_nine": 0}
    for p0, c0, c1 in itertools.product(pairs, (0, 1), (0, 1)):
        p1 = pair_step(p0, c0)
        p2 = pair_step(p1, c1)
        if p2 == (0, 0):
            assert p1[0] == 1  # (0, 0) at s forces a = 1 at s - 1
            assert p0 == (0, 0)  # and that forces (0, 0) at s - 2
            counts["zero_zero_from_a"] += 1
            counts["zero_zero_two_back"] += 1
    for p0, c0 in itertools.product(pairs, (0, 1)):
        p1 = pair_step(p0, c0)
        if p1[1] == 0:
            assert p1 == (0, 0) or p0 == (0, 0)  # b = 0 at s: the pair is (0, 0) at s or at s - 1
            counts["b_zero_cases"] += 1
    for c7, c8 in itertools.product((0, 1), (0, 1)):  # (0, 0) at 7 goes to (1, c7); if c7 = 1 then (0, 0) at 9
        p8 = pair_step((0, 0), c7)
        assert p8 == (1, c7)
        if c7 == 1:
            assert pair_step(p8, c8) == (0, 0)
        counts["seven_eight_nine"] += 1
    return counts


def _packed_rows(matrix: np.ndarray) -> np.ndarray:
    """One hashable key per row of a 0/1 matrix."""
    # matrix: (r, c)
    packed = np.ascontiguousarray(np.packbits(matrix, axis=1))  # (r, ceil(c / 8))
    return packed.view(np.dtype((np.void, packed.shape[1]))).ravel()  # (r,)


def left_count(table: np.ndarray, n: int, k: int) -> int:
    """The distinct functions of the other n - k cells after the k leftmost cells (the lowest index bits) are fixed."""
    # table: (2^n,)
    columns = table.reshape(1 << (n - k), 1 << k).T  # (2^k, 2^(n-k)), row = left word
    return len(np.unique(_packed_rows(np.ascontiguousarray(columns))))


def right_count(table: np.ndarray, n: int, k: int) -> int:
    """The distinct functions of the other n - k cells after the k rightmost cells (the highest index bits) are fixed."""
    # table: (2^n,)
    rows = table.reshape(1 << k, 1 << (n - k))  # (2^k, 2^(n-k)), row = right word
    return len(np.unique(_packed_rows(rows)))


def left_counts(t: int, table: np.ndarray | None = None) -> list[int]:
    """`left_count` for k = 1 .. 2t."""
    table = cone_table(t) if table is None else table  # (2^(2t+1),)
    return [left_count(table, 2 * t + 1, k) for k in range(1, 2 * t + 1)]


def right_counts(t: int, table: np.ndarray | None = None) -> list[int]:
    """`right_count` for k = 1 .. 2t."""
    table = cone_table(t) if table is None else table  # (2^(2t+1),)
    return [right_count(table, 2 * t + 1, k) for k in range(1, 2 * t + 1)]


def flip_leftmost_flips_center(t: int, table: np.ndarray | None = None) -> bool:
    """c_t = x_{-t} xor g(the other cells): changing the leftmost cell changes c_t for every assignment."""
    table = cone_table(t) if table is None else table  # (2^(2t+1),)
    pairs = table.reshape(-1, 2)  # (2^(2t), 2), column 0 is x_{-t} = 0
    return bool(np.all(pairs[:, 0] != pairs[:, 1]))


def screened_words(t: int) -> dict[int, list[int]]:
    """The left words (as indices of the lowest t bits, bit i = x_{-t+i}) that must share a subfunction: the even and
    the odd pattern with x_{-t} flipped, and the odd and the even pattern with x_{-t} flipped, grouped by the constant
    function of the right half that they give."""
    even = sum(int(v) << i for i, v in enumerate(left_pattern(t, False)))
    odd = sum(int(v) << i for i, v in enumerate(left_pattern(t, True)))
    return {1: [even, odd ^ 1], 0: [odd, even ^ 1]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-t", type=int, default=18, help="largest t for the constancy check of the two patterns")
    parser.add_argument("--counts", type=int, default=0, help="print subfunction counts for t = 1 .. this value")
    args = parser.parse_args()

    print("pair lemma cases:", check_pair_lemmas())
    for t in range(1, 6):
        check_pair_model(t, 50)
    print("pair model agrees with a plain run of the rule on random rows")

    print("c_t on every right half, for the even and the odd pattern on the left half (None: not constant)")
    for t in tqdm(range(1, args.max_t + 1), desc="t", file=sys.stderr):
        even, odd = (constant_value(pattern_values(t, flag)) for flag in (False, True))
        print(f"  t = {t:2d}  even: {even}  odd: {odd}")

    for t in range(1, args.counts + 1):
        table = cone_table(t)  # (2^(2t+1),)
        assert flip_leftmost_flips_center(t, table)
        print(f"t = {t}  left counts k = 1..{2 * t}: {left_counts(t, table)}")
        print(f"        right counts k = 1..{2 * t}: {right_counts(t, table)}")


if __name__ == "__main__":
    main()
