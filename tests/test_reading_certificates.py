"""The general reading certificates against a naive fixed point, the ThreeRuns ranks and direct runs."""

from __future__ import annotations

import numpy as np

from computations import three_runs
from computations.gap_traps import word_entropy
from computations.reading_certificates import (Spec, bad_table, certificate, is_forced, lean_tables, learned_words,
                                               phase_entropy, phase_readings, step, tables)
from computations.reading_modules import COLUMNS, MODULES, Module, module_text


def naive_step(w: int, width: int, center: int, beyond: int) -> int:
    """One step of a window of columns 1..width, cell by cell."""
    cells = [center] + [(w >> i) & 1 for i in range(width)] + [beyond]
    new = [cells[i - 1] ^ (cells[i] | cells[i + 1]) for i in range(1, width + 1)]
    return sum(b << i for i, b in enumerate(new))


def naive_successors(spec: Spec, p: int, w: int, s: str) -> list[tuple[bool, tuple[int, int, str]]]:
    """The two successors of a state (phase, window, stored readings as a string) and whether the step is allowed."""
    out = []
    for x in (0, 1):
        v = naive_step(w, spec.width, int(spec.block[p]), x)
        q = (p + 1) % len(spec.block)
        if p in spec.phases:
            text = s + str(w & 1)
            ok = not any(text.endswith(word) for word in spec.words)
            out.append((ok, (q, v, text[len(text) - spec.keep:] if spec.keep else "")))
        else:
            out.append((True, (q, v, s)))
    return out


def naive_certificate(spec: Spec) -> dict[tuple[int, int, str], int]:
    """The rank of every state by removing bad states and then adding backward layers, -1 where none exists."""
    texts = [format(s, f"0{spec.keep}b") if spec.keep else "" for s in range(1 << spec.keep)]
    states = {(p, w, s) for p in range(len(spec.block)) for w in range(1 << spec.width) for s in texts}
    keep = set(states)
    while True:
        drop = {st for st in keep if any(not ok or nx not in keep for ok, nx in naive_successors(spec, *st))}
        if not drop:
            break
        keep -= drop
    layer, k = {st: 0 for st in keep}, 0
    while True:
        add = {st for st in states - layer.keys() if all(nx in layer for _, nx in naive_successors(spec, *st))}
        if not add:
            return {st: layer.get(st, -1) for st in states}
        k += 1
        layer.update({st: k for st in add})


def test_step() -> None:
    w = np.arange(1 << 6, dtype=np.int64)  # (64,)
    for c in (0, 1):
        for x in (0, 1):
            assert step(w, 6, c, x).tolist() == [naive_step(int(v), 6, c, x) for v in range(1 << 6)]


def test_bad_table() -> None:
    table = bad_table(("00", "101"), 2)  # (4, 2)
    assert table.tolist() == [[True, False], [False, False], [True, True], [False, False]]


def test_matches_naive() -> None:
    """The good set and the ranks equal the naive ones, for one read phase and for several."""
    for spec in (Spec("00011", (0,), 4, ("00",)), Spec("001", (0, 1), 4, ("11", "0100")),
                 Spec("00101", (1,), 4, ("11",))):
        good, rank = certificate(spec)  # (P, 2^W, 2^keep)
        naive = naive_certificate(spec)
        for (p, w, s), r in naive.items():
            assert rank[p, w, int(s, 2) if s else 0] == r
        assert int(good.sum()) == sum(r == 0 for r in naive.values())


def test_three_runs() -> None:
    """For 001 read at the second white step the ranks are those of three_runs, and the tables of ThreeRuns."""
    for width in (7, 10):
        good, rank = certificate(Spec("001", (1,), width, three_runs.WORDS))
        good3, rank3 = three_runs.ranks(width)
        assert np.array_equal(good, good3) and np.array_equal(rank, rank3)
    assert tables(rank3, 6) == three_runs.tables(rank3)


def test_forced_00011() -> None:
    """Block 00011 read at its first white step: entry into no 00 is forced at width 5 and not at width 4."""
    assert is_forced(Spec("00011", (0,), 4, ("00",)))[0] is False
    assert is_forced(Spec("00011", (0,), 5, ("00",))) == (True, 13)


def test_direct_run() -> None:
    """A random half driven by 00011 reads no 00 at the first white step once the second reading is at step 13."""
    rng = np.random.default_rng(5)
    for ph in range(5):
        half = int(rng.integers(0, 1 << 62)) | (int(rng.integers(0, 1 << 62)) << 62)
        reads = [b for p, b in phase_readings("00011", ph, half, 300) if p == 0]
        times = [t for t in range(300) if (t + ph) % 5 == 0]
        assert len(reads) == len(times)
        assert not any(reads[i] == reads[i + 1] == 0 for i in range(len(reads) - 1) if times[i + 1] >= 13)


def test_learned_words() -> None:
    runs = [[(0, b) for b in [1, 0, 1, 1, 0, 1, 0, 1, 1]]]
    assert learned_words(runs, (0,), 3) == ["00", "111"]


def test_entropy() -> None:
    assert abs(phase_entropy(("11",), 1, {}) - word_entropy(("11",))) < 1e-9
    assert abs(phase_entropy(("11",), 1, {}) - np.log2((1 + 5 ** 0.5) / 2)) < 1e-9
    assert abs(phase_entropy((), 2, {1: 0}) - 0.5) < 1e-9
    assert abs(phase_entropy((), 1, {}) - 1.0) < 1e-9


def test_direct_run_00001() -> None:
    """Random halves driven by 00001 read no 11 and no 1001 at the first white step once the last reading is at step
    29, as Runs00001 states."""
    rng = np.random.default_rng(7)
    for ph in range(5):
        half = int(rng.integers(0, 1 << 62)) | (int(rng.integers(0, 1 << 62)) << 62)
        reads = [b for p, b in phase_readings("00001", ph, half, 400) if p == 0]
        times = [t for t in range(400) if (t + ph) % 5 == 0]
        text = "".join(map(str, reads))
        for word in ("11", "1001"):
            assert all(text[i:i + len(word)] != word for i in range(len(text) - len(word) + 1)
                       if times[i + len(word) - 1] >= 29)


def test_runs00001_module() -> None:
    """The module Runs00001.lean is the text the generator writes from the ranks, and its tables are the ranks."""
    spec = Spec("00001", (0,), 12, ("11", "1001"))
    _, rank = certificate(spec)  # (5, 4096, 8)
    assert int(rank.min()) == 0 and int(rank.max()) == 29
    path = COLUMNS / "Runs00001.lean"
    assert lean_tables(path) == tables(rank, 5)
    assert module_text(MODULES["Runs00001"]) == path.read_text(encoding="utf-8")


def test_module_text_other_phase() -> None:
    """At a read phase other than 0 the generator writes the offsets of that phase."""
    mod = Module(name="Test", block="00101", q=3, width=6, words=("101",), title="t", summary="s", pred="P",
                 pred_doc="d", headline="h", headline_doc="H.", evolve_doc="E.", step_name="third white step")
    text = module_text(mod)
    assert "def reading (R : Nat → Bool) (ph i : Nat) : Bool := drv (ctr ph) R (5 * i + (3 + 5 - ph % 5) % 5) 1" in text
    assert "theorem no_101_time (u : Nat) (hu : 2 ≤ u) (hp : (u + ph) % 5 = 3)" in text
    assert "P (fun i => evolve init (T + 5 * i + 3) 1)" in text
