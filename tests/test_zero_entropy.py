"""The zero-entropy test of word lists, the forced lists with tagged words and the window-graph obstruction against
independent checks: dense eigenvalues, naive fixed points, the finite game, brute-force factorizations and cell-by-cell
walks."""

from __future__ import annotations

import itertools

import numpy as np

from computations import game
from computations.reading_certificates import Spec, is_forced
from computations.zero_entropy import (analyze, check_witness, code_bound, completes, driven_period, factor_counts, forced,
                                       greedy_code, is_code, learned, naive_classes, naive_walk, sft_entropy, sft_graph, sft_is_zero, witness)


def dense_radius(words: tuple[tuple[str, int], ...], k: int, constants: dict[int, int] | None = None,
                 frame: int = 1) -> float:
    """The spectral radius of the de Bruijn graph built here by strings, from numpy's dense eigenvalues."""
    constants = constants or {}
    keep = max([len(u) for u, _ in words] + [1]) - 1
    texts = ["".join(t) for t in itertools.product("01", repeat=keep)]
    m = k * frame
    index = {(j, t): i for i, (j, t) in enumerate(itertools.product(range(m), texts))}
    a = np.zeros((len(index), len(index)))  # (nodes, nodes)
    for (j, t), i in index.items():
        for b in "01":
            if j in constants and str(constants[j]) != b:
                continue
            text = t + b
            if any(text.endswith(u) and (pos < 0 or (j % k - len(u) + 1) % k == pos) for u, pos in words):
                continue
            a[i, index[((j + 1) % m, text[1:] if keep else "")]] += 1
    return float(max(abs(np.linalg.eigvals(a)))) if a.size else 0.0


def test_sft_known() -> None:
    golden = sft_graph((("11", -1),), 1)
    assert not sft_is_zero(golden)
    assert abs(sft_entropy(golden) - np.log2((1 + 5 ** 0.5) / 2)) < 1e-6
    alternating = sft_graph((("00", -1), ("11", -1)), 1)
    assert sft_is_zero(alternating) and sft_entropy(alternating) < 1e-6
    half = sft_graph((("1", 0),), 2)  # the reading at position 0 is white, the other free
    assert not sft_is_zero(half) and abs(sft_entropy(half) - 0.5) < 1e-6
    fixed = sft_graph((), 2, constants={0: 0, 1: 1})  # both positions fixed: one periodic sequence
    assert sft_is_zero(fixed)
    eventually = sft_graph((("10", -1),), 1)  # 1s then 0s: two cycles joined by one edge
    assert sft_is_zero(eventually)


def test_sft_zero_against_eigenvalues() -> None:
    rng = np.random.default_rng(1)
    zeros = 0
    for _ in range(80):
        k = int(rng.integers(1, 3))
        words = []
        for _ in range(int(rng.integers(1, 5))):
            ln = int(rng.integers(1, 5))
            words.append((format(int(rng.integers(0, 1 << ln)), f"0{ln}b"), int(rng.integers(-1, k))))
        words_t = tuple(words)
        radius = dense_radius(words_t, k)
        graph = sft_graph(words_t, k)
        zero = sft_is_zero(graph)
        assert zero == (radius < 1 + 1e-6)
        zeros += zero
        if radius > 1e-9:
            assert abs(sft_entropy(graph) - np.log2(max(radius, 1.0))) < 1e-4
    assert zeros > 5


def test_completes() -> None:
    assert completes("0110", ("10", -1), 3, 2)
    assert completes("0110", ("10", 0), 1, 2)  # the word starts at position 0
    assert not completes("0110", ("10", 1), 1, 2)


def naive_forced(block: str, width: int, words: tuple[tuple[str, int], ...]) -> bool:
    """Forced entry by sets of states (phase, window, stored readings as a string), cell by cell."""
    whites = [p for p, c in enumerate(block) if c == "0"]
    k, keep = len(whites), max(len(u) for u, _ in words) - 1

    def successors(p: int, w: int, s: str) -> list[tuple[bool, tuple[int, int, str]]]:
        out = []
        for x in (0, 1):
            cells = [int(block[p])] + [(w >> i) & 1 for i in range(width)] + [x]
            v = sum((cells[i - 1] ^ (cells[i] | cells[i + 1])) << (i - 1) for i in range(1, width + 1))
            q = (p + 1) % len(block)
            if p in whites:
                text = s + str(w & 1)
                ok = not any(completes(text, u, whites.index(p), k) for u in words)
                out.append((ok, (q, v, text[len(text) - keep:] if keep else "")))
            else:
                out.append((True, (q, v, s)))
        return out

    texts = ["".join(t) for t in itertools.product("01", repeat=keep)]
    states = {(p, w, s) for p in range(len(block)) for w in range(1 << width) for s in texts}
    good = set(states)
    while True:
        drop = {st for st in good if any(not ok or nx not in good for ok, nx in successors(*st))}
        if not drop:
            break
        good -= drop
    if not good:
        return False
    done = set(good)
    while True:
        add = {st for st in states - done if all(nx in done for _, nx in successors(*st))}
        if not add:
            return done == states
        done |= add


def test_forced_against_naive() -> None:
    cases = [("001", 5, (("11", -1),)), ("001", 5, (("1", 0),)), ("001", 5, (("1", 1),)),
             ("0001", 4, (("11", -1), ("101", 2))), ("011", 5, (("00", -1),)), ("00101", 4, (("11", 0), ("010", 1)))]
    for block, width, words in cases:
        assert forced(block, width, words)[0] == naive_forced(block, width, words), (block, words)
    # untagged words agree with reading_certificates at every white phase
    for block, width, words in [("001", 8, ("11",)), ("00001", 7, ("11", "1001")), ("0011", 7, ("00",))]:
        phases = tuple(p for p, c in enumerate(block) if c == "0")
        assert forced(block, width, tuple((u, -1) for u in words))[0] == is_forced(Spec(block, phases, width, words))[0]


def test_learned() -> None:
    # block 001: positions 0 and 1; the readings alternate 0, 1 at positions 0, 1
    runs = [[(0, 0), (1, 1)] * 20]
    words = learned("001", runs, 3)
    assert ("1", 0) in words and ("0", 1) in words
    assert all(len(u) == 1 for u, _ in words)


def test_analyze_against_game() -> None:
    for block, width in [("001", 6), ("0001", 6), ("00000001", 6), ("011", 7), ("00101", 5), ("0000000101", 5)]:
        a = analyze(block, width)
        assert (a.phase_mixed == 0) == (game.bad_pairs(block, width) == 0), block
        found = game.component_periods(block, width)
        assert a.components == len(found)
        assert a.class_mixed == sum(1 for part in found if part[3]), block


def test_is_code_brute_force() -> None:
    rng = np.random.default_rng(3)

    def factorizations(words: list[str], text: str) -> int:
        count = [1] + [0] * len(text)
        for i in range(1, len(text) + 1):
            count[i] = sum(count[i - len(u)] for u in words if len(u) <= i and text[i - len(u):i] == u)
        return count[-1]

    for _ in range(60):
        words = sorted({format(int(rng.integers(0, 1 << ln)), f"0{ln}b")
                        for ln in rng.integers(1, 5, size=int(rng.integers(2, 4)))})
        unique = all(factorizations(words, "".join(seq)) == 1
                     for r in range(1, 5) for seq in itertools.product(words, repeat=r))
        assert is_code(words) == unique, words
    assert abs(code_bound([1, 1]) - 1.0) < 1e-9
    assert abs(code_bound([1, 2]) - np.log2((1 + 5 ** 0.5) / 2)) < 1e-9
    assert greedy_code(["01", "0101", "10"]) == [0, 2]


def test_witness_and_forced_list() -> None:
    a = analyze("001", 12)
    assert a.class_mixed > 0 and a.root >= 0
    wit = witness("001", 12, a.root, walks=100, roots=3)
    assert check_witness(wit) and wit.bound > 0
    # naive_walk agrees with a cycle of the code and with the step of the module
    p, w, text = naive_walk("001", 12, wit.phase, wit.window, wit.inputs[wit.code[0]])
    assert (p, w) == (wit.phase, wit.window) and text == wit.labels[wit.code[0]]
    # a list forced at width 12 avoids every concatenation of the code, so its entropy is at least the bound
    words = (("11", -1),)
    assert forced("001", 12, words)[0]
    for i, j in itertools.product(wit.code, repeat=2):
        assert "11" not in wit.labels[i] + wit.labels[j] + wit.labels[i]
    assert sft_entropy(sft_graph(words, 2)) >= wit.bound - 1e-9


def test_factor_counts() -> None:
    periodic = [[(0, b) for b in [0, 1, 1] * 30]]
    assert factor_counts(periodic, (1, 2, 5)) == [2, 3, 3]
    rng = np.random.default_rng(0)
    free = [[(0, int(b)) for b in rng.integers(0, 2, 4000)]]
    assert factor_counts(free, (4,)) == [16]


def test_naive_classes_against_analyze() -> None:
    for block, width in [("001", 7), ("0001", 6), ("00000001", 6), ("0000000001", 6), ("011", 6)]:
        a = analyze(block, width)
        found = naive_classes(block, width)
        assert len(found) == a.components
        assert sum(1 for x in found if x[2]) == a.phase_mixed
        assert sum(1 for x in found if x[3]) == a.class_mixed
        assert sorted((size, cyc) for size, cyc, _, _ in found) == \
            sorted((size, cyc) for size, cyc, _, _ in game.component_periods(block, width))


def test_driven_period() -> None:
    # a white right half beside a white center stays white: period one block
    assert driven_period("0", 0, 200, 40) == 1
    # one black cell beside a white center moves right and leaves column 1 white
    assert driven_period("00", 1, 200, 40) == 2
    # beside 001 the half of one black cell: some period found or 0, and a found period divides the tail check
    p = driven_period("001", 1, 400, 120)
    assert p == 0 or p % 3 == 0
