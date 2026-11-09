"""Late seeds and the left cut for every t: plain runs, the left-edge frame, the shift and the module's check."""

from __future__ import annotations

import random
import re
from pathlib import Path

from computations import late_seed_cut as ls


def plain_center(cells: list[int]) -> int:
    """c_t from the 2t + 1 cone cells x_{-t} .. x_t by running the rule on a list, one cell at a time."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def cells_of(a: int, t: int, r: int, P: int) -> list[int]:
    """The 2t + 1 cone cells of the row with the bits of P left of the cut and the bits of r from the cut on."""
    return [(P >> k) & 1 for k in range(a)] + [(r >> k) & 1 for k in range(2 * t + 1 - a)]


def test_centers_against_plain_runs() -> None:
    """`late_cen`, the bit-sliced `centers_plain` and the packed `late_col` agree with plain list runs."""
    rng = random.Random(30)
    for _ in range(60):
        t = rng.randint(2, 12)
        a = rng.randint(1, min(7, 2 * t))
        r = rng.getrandbits(2 * t + 1 - a) if rng.random() < 0.5 else 1 << rng.randint(0, 2 * t - a)
        sliced = ls.centers_plain(a, t, r)
        packed = ls.late_col(a, t, r)
        for P in range(1 << a):
            value = plain_center(cells_of(a, t, r, P))
            assert ls.late_cen(a, t, r, P) == value
            assert (sliced >> P) & 1 == value
            assert (packed >> P) & 1 == value


def test_edge_frame_is_the_seed() -> None:
    """Bit j of the edge frame is the single cell's row j places right of its left edge (a plain run), and a black cell
    at mu is the edge frame shifted (`nevo_two_pow`)."""
    row = [1]  # cells -s .. s
    for s in range(30):
        assert ls.edge_frame(s) == sum(b << j for j, b in enumerate(row))
        row = [plain_center(([0, 0] + row + [0, 0])[i:i + 3]) for i in range(len(row) + 2)]
    for mu in range(0, 25):
        for s in range(0, 20):
            assert ls.nevo(1 << mu, s) == (ls.edge_frame(s) << mu) >> (2 * s)


def test_edge_periods() -> None:
    """The period data the module checks in the kernel: the low J bits repeat with period p from s0 on, and not from
    s0 - 1."""
    for J, p, s0 in [(3, 1, 2), (5, 2, 2), (9, 4, 2), (11, 4, 6), (17, 4, 16), (19, 4, 20), (25, 4, 27), (31, 8, 33)]:
        assert ls.edge_period(J) == (p, s0)
        mask = (1 << J) - 1
        assert ls.edge_frame(s0 + p) & mask == ls.edge_frame(s0) & mask
        assert ls.edge_frame(s0 + p - 1) & mask != ls.edge_frame(s0 - 1) & mask


def test_shift_and_suffix() -> None:
    """`lateCen_shift`: from t0 on, the center at t + p with the seed moved 2p cells right is the center at t for the
    left cells run p steps first; `lateCen_suffix`: the white stretch runs the left cells on their own."""
    a, R, J, p, s0 = 4, 3, 9, 4, 2
    t0 = s0 + R + 1 + (a + 1) // 2
    for t in range(t0, t0 + 6):
        for Rp in range(R + 1):
            for d in (0, 1):
                r = 1 << ls.seed_pos(a, t, Rp, d)
                r2 = 1 << ls.seed_pos(a, t + p, Rp, d)
                for P in range(1 << a):
                    assert ls.late_cen(a, t + p, r2, P) == ls.late_cen(a, t, r, ls.nevo(P, p))
                    m = min(t, (a + 1) // 2 + R + 1)
                    assert ls.late_cen(a, t, r, P) == ls.late_cen(a, m, ls.nevo(r, t - m), ls.nevo(P, t - m))


def test_scan_small() -> None:
    """t_f(a) + 1 and R_a for a = 2 .. 6 are the module's `lateStart` and `lateR`."""
    starts, Rs = [3, 4, 6, 7, 10], [0, 1, 3, 4, 7]
    for a in range(2, 7):
        tf, Ra, _ = ls.scan(a, 22)
        assert (tf + 1, Ra) == (starts[a - 2], Rs[a - 2])


def test_check_mirror() -> None:
    """The mirrored kernel check passes on the range the module checks for a = 4 and 5, fails just below `lateStart`,
    and agrees with the plain-run separation."""
    for a, (tA, R, J, p, s0) in [(4, (6, 3, 9, 4, 2)), (5, (7, 4, 11, 4, 6))]:
        t0 = s0 + R + 1 + (a + 1) // 2
        for t in range(tA, t0 + p):
            assert ls.late_check(a, t, R)
            assert ls.separates(a, t, R)
        assert not ls.late_check(a, tA - 1, R)
        assert not ls.separates(a, tA - 1, R)


def test_module_parameters() -> None:
    """The thresholds, the largest R and the period data written into LateSeedCut are those computed here (a <= 6),
    and every edge period check of the module states a repetition that holds."""
    text = (Path(__file__).resolve().parents[1] / "Rule30Open" / "Complexity" / "LateSeedCut.lean").read_text()
    start = dict((int(a), int(v)) for a, v in re.findall(r"\| (\d+) => (\d+)", text.split("def lateStart")[1].split("def ")[0]))
    rmax = dict((int(a), int(v)) for a, v in re.findall(r"\| (\d+) => (\d+)", text.split("def lateR")[1].split("theorem ")[0]))
    for a in range(2, 7):
        tf, Ra, _ = ls.scan(a, 22)
        assert (start[a], rmax[a]) == (tf + 1, Ra)
    for s0, p, J in re.findall(r"edgeFrame \((\d+) \+ (\d+)\) % 2 \^ (\d+)", text):
        s0, p, J = int(s0), int(p), int(J)
        assert ls.edge_frame(s0 + p) % (1 << J) == ls.edge_frame(s0) % (1 << J)
        assert ls.edge_period(J) == (p, s0)


def test_below_threshold() -> None:
    """Below `lateStart` the white and every single black cell completion fail (a = 4, 5, 6), and at a = 7, t = 10
    they separate."""
    for a, ts in [(4, [5]), (5, [6]), (6, [7, 8, 9])]:
        assert not any(ls.separates_all_single(a, t) for t in ts)
    assert ls.separates_all_single(7, 10) and not ls.separates_all_single(7, 11)
