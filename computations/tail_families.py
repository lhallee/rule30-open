"""Tail families `0^q t` after a white run, with windows of 14 and 20 cells, and the white cycle as sets.

`limit_windows` decides the family `0^q t` for every `q` from the preperiod and period of the relation "one step
beside a 0" on windows (`limit_windows.white_cycle`), whose powers it holds as one bit set per window: `2^w` rows of
`2^w` bits, which does not fit in memory at 20 cells. Here the relation is followed one window at a time
(`singleton_orbit`): row `u` of the power `j` is the set of windows reached from `u` in `j` white steps, and the
powers repeat from `p` with period `d` exactly when every row does, so `p` is the largest preperiod of a row and `d`
the least common multiple of their periods (`white_cycle_sets`). With them `tail_table` decides each tail as
`limit_windows.tail_thresholds` does, at any width that fits one set of windows.

`cycle_certificate` is the check of the Lean module `Rule30Open.Columns.TailFamilies14`: it follows `k` periods of
`0^N t` from all windows and asks that `d` more white steps map each set after the white run into itself, which
proves `0^(N + d m) t` for every `m` without the preperiod. `lean_pieces` chooses the pieces of each tail at 14 cells,
and `lean_section` writes them as Lean.

    python -m computations.tail_families --cycle 20                 # preperiod and period at 20 cells, about 9 min
    python -m computations.tail_families --tails 8 --width 20 --preperiod 84 --workers 2   # the tails, about 30 min
    python -m computations.tail_families --lean 6                   # the pieces of TailFamilies14 at 14 cells
    python -m computations.tail_families --lean 6 --step 1          # the same with a fixed point of the white sets
    python -m computations.tail_families --union 6                  # the kit main branch's union check, 14 cells
    python -m computations.tail_families --certify 10101 --width 20 --upto 90     # one tail, by residue class
    python -m computations.tail_families --good 1100001 --width 22 --upto 100     # one tail, q by q
"""

from __future__ import annotations

import argparse
import math
import multiprocessing
import sys

import numpy as np
from tqdm.auto import tqdm

from computations.limit_windows import block_of, is_good, limit_sets, tails_up_to, window_moves
from computations.rule30 import distinct


def singleton_orbit(white: np.ndarray, start: int) -> tuple[int, int]:
    """The preperiod and period of the sets reached from the window `start` by white steps; `white` (shape (n, 2))
    holds the two windows each window becomes beside a 0. The sets are sorted arrays; a repeat is found by a
    dictionary of their bytes."""
    members = np.array([start], dtype=white.dtype)  # (s,)
    seen: dict[bytes, int] = {}
    step = 0
    while True:
        key = members.tobytes()
        if key in seen:
            return seen[key], step - seen[key]
        seen[key] = step
        members = distinct(white[members].reshape(-1))  # (s',)
        step += 1


def _orbit_chunk(args: tuple[int, int, int]) -> tuple[int, int]:
    """The largest preperiod and the least common multiple of the periods of the windows `lo` to `hi - 1` (module
    level, for worker processes)."""
    width, lo, hi = args
    white = window_moves(width)[0].astype(np.int32)  # (n, 2)
    worst, period = 0, 1
    for start in range(lo, hi):
        pre, per = singleton_orbit(white, start)
        worst, period = max(worst, pre), math.lcm(period, per)
    return worst, period


def white_cycle_sets(width: int, workers: int = 1, chunks: int = 256) -> tuple[int, int]:
    """The preperiod p and period d of the powers of the white relation on windows of `width` cells, one window at a
    time: the powers from p on repeat with period d, and p and d are the least such."""
    n = 1 << width
    size = max(1, n // chunks)
    tasks = [(width, lo, min(n, lo + size)) for lo in range(0, n, size)]
    pool = multiprocessing.get_context("spawn").Pool(workers) if workers > 1 else None
    results = pool.imap_unordered(_orbit_chunk, tasks) if pool else map(_orbit_chunk, tasks)
    worst, period = 0, 1
    for pre, per in tqdm(results, total=len(tasks), desc=f"white orbits, {width} cells", unit="chunk",
                         file=sys.stderr, mininterval=5):
        worst, period = max(worst, pre), math.lcm(period, per)
    if pool:
        pool.close()
    return worst, period


def largest_limit(block: str, moves: np.ndarray) -> int:
    """The largest number of windows in a limit set of `block`, over its phases."""
    return max(len(members) for members in limit_sets(block, moves))


def tail_row(args: tuple[str, int, int]) -> tuple[str, list[bool], int]:
    """Goodness of `0^q tail` for q = 1 .. top, and the largest limit set over the good q (module level, for worker
    processes)."""
    tail, width, top = args
    moves = window_moves(width)
    good, largest = [], 0
    for q in range(1, top + 1):
        flag = is_good(block_of(q, tail), moves)
        good.append(flag)
        if flag:
            largest = max(largest, largest_limit(block_of(q, tail), moves))
    return tail, good, largest


def threshold(good: list[bool]) -> tuple[int | None, list[int]]:
    """The least q0 with every q from q0 to the end good (None if the last is bad), and the good q below q0;
    `good[q - 1]` is the goodness of q."""
    q0 = None
    for q in range(len(good), 0, -1):
        if not good[q - 1]:
            break
        q0 = q
    return q0, [q for q in range(1, len(good) + 1) if good[q - 1] and (q0 is None or q < q0)]


def tail_table(tails: list[str], width: int, preperiod: int, period: int, workers: int = 1
               ) -> dict[str, tuple[int | None, list[int], int]]:
    """For each tail, the least `q0` such that `0^q tail` is good for every `q >= q0` (None if none), the sporadic good
    `q` below it and the largest limit set of a good `q`. For `q >= p + d` goodness depends only on q mod d, so the
    `q` up to p + 2 d - 1 decide every `q`."""
    top = preperiod + 2 * period - 1
    tasks = [(tail, width, top) for tail in tails]
    pool = multiprocessing.get_context("spawn").Pool(workers) if workers > 1 else None
    rows = pool.imap(tail_row, tasks) if pool else map(tail_row, tasks)
    out = {}
    for tail, good, largest in tqdm(rows, total=len(tasks), desc=f"tails, {width} cells", unit="tail",
                                    file=sys.stderr, mininterval=5):
        q0, sporadic = threshold(good)
        out[tail] = (q0, sporadic, largest)
    if pool:
        pool.close()
    return out


def image(members: np.ndarray, moves: np.ndarray, col: int) -> np.ndarray:
    """The windows reached in one step beside `col` from the windows marked in `members` (shape (n,), bool)."""
    out = np.zeros(moves.shape[1], dtype=bool)  # (n,)
    index = np.flatnonzero(members)  # (s,)
    out[moves[col, index, 0]] = True
    out[moves[col, index, 1]] = True
    return out


def read(members: np.ndarray, moves: np.ndarray, word: str) -> np.ndarray:
    """The windows after the column reads `word` from the windows marked in `members` (shape (n,), bool)."""
    for ch in word:
        members = image(members, moves, int(ch))
    return members


def subset(small: np.ndarray, large: np.ndarray) -> bool:
    """Whether every window marked in `small` is marked in `large` (both shape (n,), bool)."""
    return not bool(np.any(small & ~large))


def known(members: np.ndarray) -> bool:
    """Whether every window marked in `members` (shape (n,), bool) has the same first cell."""
    first = np.flatnonzero(members) & 1  # (s,)
    return len(first) == 0 or bool(first.min() == first.max())


def cycle_certificate(tail: str, start: int, step: int, periods: int, moves: np.ndarray) -> bool:
    """The Lean check `cycleCert`: from all windows, `periods` periods of `0^start tail`; after each white run the set
    Y must satisfy `image of Y under step more white steps is inside Y`; at the last set X the next period must map
    into X, the first cell must be known after each of the first start + step white steps and at each 0 of the tail.
    True proves `0^(start + step m) tail` for every m (with step 0, the word `0^start tail` alone)."""
    members = np.ones(moves.shape[1], dtype=bool)  # (n,)
    for left in range(periods, -1, -1):
        after = read(members, moves, "0" * start)  # (n,)
        if not subset(read(after, moves, "0" * step), after):
            return False
        if left:
            members = read(after, moves, tail)
    if not subset(read(after, moves, tail), members):
        return False
    state = members
    for _ in range(start + step):
        if not known(state):
            return False
        state = image(state, moves, 0)
    state = after
    for ch in tail:
        if ch == "0" and not known(state):
            return False
        state = image(state, moves, int(ch))
    return True


def white_union(members: np.ndarray, moves: np.ndarray, least: int) -> np.ndarray:
    """The windows after at least `least` white steps from the windows marked in `members` (shape (n,), bool): the
    union of the white images from `least` on, until it stops growing."""
    current = read(members, moves, "0" * least)  # (n,)
    union = current.copy()  # (n,)
    while True:
        current = image(current, moves, 0)
        grown = union | current  # (n,)
        if np.array_equal(grown, union):
            return union
        union = grown


def union_certificate(tail: str, least: int, periods: int, moves: np.ndarray) -> bool:
    """The check of the kit main branch's `paramStripCert` for `0^r tail`, every r >= `least` at once: one period is
    the union of all white runs of at least `least` steps, then the tail; from all windows, `periods` periods give
    S0; the next period must map into S0, and the first cell must be known after each of the first least - 1 white
    steps, on the union from least - 1 steps on, and at each 0 of the tail."""
    members = np.ones(moves.shape[1], dtype=bool)  # (n,)
    for _ in range(periods):
        members = read(white_union(members, moves, least), moves, tail)
    after = white_union(members, moves, least)  # (n,)
    if not subset(read(after, moves, tail), members):
        return False
    state = members
    for _ in range(least - 1):
        if not known(state):
            return False
        state = image(state, moves, 0)
    if not known(white_union(members, moves, least - 1)):
        return False
    state = after
    for ch in tail:
        if ch == "0" and not known(state):
            return False
        state = image(state, moves, int(ch))
    return True


def least_periods(tail: str, start: int, step: int, moves: np.ndarray, most: int) -> int | None:
    """The least number of periods, up to `most`, at which `cycle_certificate` holds, or None."""
    for periods in range(most + 1):
        if cycle_certificate(tail, start, step, periods, moves):
            return periods
    return None


def lean_pieces(tail: str, q0: int, moves: np.ndarray, step: int = 4, most: int = 6
                ) -> tuple[int, list[tuple[int, int, int]]]:
    """Pieces `(N, d, k)` with `cycle_certificate` that cover every q >= q0: for each residue modulo `step` the least
    N >= q0 that passes with d = step, then each q in [q0, B) that no piece of period `step` covers, alone (d = 0);
    B is the largest N of period `step`. Returns B and the pieces."""
    pieces = []
    for residue in range(step):
        start = q0 + residue
        while (periods := least_periods(tail, start, step, moves, most)) is None:
            start += step
        pieces.append((start, step, periods))
    bound = max(start for start, _, _ in pieces)
    for q in range(q0, bound):
        if any(d == step and start <= q and (q - start) % step == 0 for start, d, _ in pieces):
            continue
        periods = least_periods(tail, q, 0, moves, most)
        assert periods is not None, f"0^{q} {tail} has no certificate in {most} periods"
        pieces.append((q, 0, periods))
    return bound, pieces


def lean_word(tail: str) -> str:
    """The tail as a Lean list of Booleans."""
    return "[" + ", ".join("true" if ch == "1" else "false" for ch in tail) + "]"


def lean_section(tail: str, q0: int, bound: int, pieces: list[tuple[int, int, int]]) -> str:
    """The Lean theorem of one tail: its `tailCert` at 14 cells, checked by the kernel, eight pieces a line."""
    items = [f"({start}, {step}, {periods})" for start, step, periods in pieces]
    lines = [", ".join(items[i:i + 8]) for i in range(0, len(items), 8)]
    listed = ",\n      ".join(lines)
    return (f"/-- `0^q {tail}` for every `q ≥ {q0}`. -/\n"
            f"theorem cert_{tail} : tailCert 14 {lean_word(tail)} {q0} {bound}\n"
            f"    [{listed}] = true := by\n"
            f"  decide +kernel\n")


def lean_table(rows: list[tuple[str, int]]) -> str:
    """The Lean list of the tails with their thresholds, and the theorem that each has its `tailCert`."""
    listed = ",\n  ".join(f"({lean_word(tail)}, {q0})" for tail, q0 in rows)
    cases = " |\n    ".join(" | ".join("rfl" for _ in rows[i:i + 10]) for i in range(0, len(rows), 10))
    proofs = "\n".join(f"  · exact ⟨_, _, cert_{tail}⟩" for tail, _ in rows)
    return ("/-- The tails of one to six cells that start and end with 1, other than `10101`, with their thresholds "
            "at\n14 cells. -/\n"
            f"def thresholds14 : List (List Bool × Nat) := [\n  {listed}]\n\n"
            f"/-- Each tail of `thresholds14` has a tail certificate from its threshold. -/\n"
            f"theorem thresholds14_cert : ∀ e ∈ thresholds14, ∃ B ps, tailCert 14 e.1 e.2 B ps = true := by\n"
            f"  intro e he\n"
            f"  simp only [thresholds14, List.mem_cons, List.not_mem_nil, or_false] at he\n"
            f"  obtain {cases} := he\n"
            f"{proofs}\n")


def certify_classes(tail: str, width: int, upto: int, step: int, most: int, least: int = 1
                    ) -> dict[int, tuple[int, int] | None]:
    """For each residue of `step`, the least N in [`least`, `upto`] in that class with a cycle certificate of
    `0^N tail` at `width` cells and its number of periods, or None."""
    moves = window_moves(width)
    out: dict[int, tuple[int, int] | None] = {}
    for residue in tqdm(range(step), desc=f"{tail}, {width} cells", unit="class", file=sys.stderr, mininterval=5):
        out[residue] = None
        first = least + (residue - least) % step
        for start in range(first, upto + 1, step):
            periods = least_periods(tail, start, step, moves, most)
            if periods is not None:
                out[residue] = (start, periods)
                break
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cycle", type=int, default=0, help="preperiod and period of the white relation at this width")
    parser.add_argument("--tails", type=int, default=0, help="thresholds of every tail of up to this many cells")
    parser.add_argument("--width", type=int, default=20)
    parser.add_argument("--preperiod", type=int, default=0, help="skip --cycle: the preperiod at --width")
    parser.add_argument("--period", type=int, default=4)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--lean", type=int, default=0, help="the Lean pieces of the tails of up to this many cells")
    parser.add_argument("--step", type=int, default=4, help="the period of the pieces of --lean (4 writes the Lean)")
    parser.add_argument("--union", type=int, default=0, help="the least white run of the union check, at 14 cells, "
                                                               "for the tails of up to this many cells")
    parser.add_argument("--good", default="", help="a tail: the q up to --upto at which 0^q tail is good at --width")
    parser.add_argument("--certify", default="", help="a tail: cycle certificates by residue class at --width")
    parser.add_argument("--upto", type=int, default=40, help="the largest start --certify tries")
    parser.add_argument("--least", type=int, default=1, help="the least start --certify tries")
    args = parser.parse_args()

    if args.cycle:
        print(f"white relation at {args.cycle} cells: preperiod, period = "
              f"{white_cycle_sets(args.cycle, args.workers)}", flush=True)
    if args.tails:
        preperiod, period = ((args.preperiod, args.period) if args.preperiod
                             else white_cycle_sets(args.width, args.workers))
        table = tail_table(tails_up_to(args.tails), args.width, preperiod, period, args.workers)
        print(f"{args.width} cells: preperiod {preperiod}, period {period}, q up to {preperiod + 2 * period - 1}")
        for tail, (q0, sporadic, largest) in table.items():
            print(f"{tail}: q0 = {q0}, sporadic {sporadic}, largest limit set {largest}")
        for length in range(1, args.tails + 1):
            row = {t: v for t, v in table.items() if len(t) == length}
            worst = max((v[0] for v in row.values() if v[0] is not None), default=None)
            none = [t for t, v in row.items() if v[0] is None]
            print(f"tails of {length} cells: {len(row) - len(none)} of {len(row)} have a threshold, the largest is "
                  f"{worst}; no threshold: {none}; largest limit set {max(v[2] for v in row.values())}")
    if args.lean:
        from computations.limit_windows import tail_thresholds
        tails = [t for t in tails_up_to(args.lean) if t != "10101"]
        thresholds = tail_thresholds(tails, 14)
        moves = window_moves(14)
        counts = [0, 0]
        for tail in tqdm(tails, desc="Lean pieces", unit="tail", file=sys.stderr, mininterval=5):
            bound, pieces = lean_pieces(tail, thresholds[tail][0], moves, args.step)
            counts[0] += sum(step > 0 for _, step, _ in pieces)
            counts[1] += sum(step == 0 for _, step, _ in pieces)
            if args.step == 4:
                print(lean_section(tail, thresholds[tail][0], bound, pieces))
            else:
                print(f"-- {tail}: threshold {thresholds[tail][0]}, pieces {pieces}")
        if args.step == 4:
            print(lean_table([(tail, thresholds[tail][0]) for tail in tails]))
        print(f"-- {counts[0] + counts[1]} pieces, {counts[0]} of period {args.step} and {counts[1]} single words")
    if args.union:
        from computations.limit_windows import tail_thresholds
        tails = [t for t in tails_up_to(args.union) if t != "10101"]
        thresholds = tail_thresholds(tails, 14)
        moves = window_moves(14)
        for tail in tqdm(tails, desc="union check", unit="tail", file=sys.stderr, mininterval=5):
            least = thresholds[tail][0]
            while not any(union_certificate(tail, least, periods, moves) for periods in (1, 2, 3)):
                least += 1
            print(f"{tail}: threshold {thresholds[tail][0]}, union check from {least}", flush=True)
    if args.good:
        _, good, largest = tail_row((args.good, args.width, args.upto))
        print(f"0^q {args.good} at {args.width} cells, q up to {args.upto}: good for {threshold(good)[0]} on, sporadic "
              f"{threshold(good)[1]}, bad for {[q for q in range(1, args.upto + 1) if not good[q - 1]]}; largest "
              f"limit set {largest}", flush=True)
    if args.certify:
        found_classes = certify_classes(args.certify, args.width, args.upto, args.period, 8, args.least)
        for residue, found in found_classes.items():
            print(f"{args.certify} at {args.width} cells, q = {residue} mod {args.period}: "
                  + (f"every q >= {found[0]} in the class, {found[1]} periods" if found else
                     f"no certificate up to {args.upto}"), flush=True)


if __name__ == "__main__":
    main()
