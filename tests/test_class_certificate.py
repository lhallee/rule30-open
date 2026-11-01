"""The certificate of the game with cyclic classes against independent checks: the node-by-node conditions written cell
by cell, the components and cyclic periods of `game.component_periods`, and the tries read back as Lean reads them."""

from __future__ import annotations

import numpy as np
import pytest

from computations import class_certificate as cc
from computations import game


def parse(text: str) -> tuple[object, str]:
    """A trie written by `cc.trie`, read back as nested tuples; returns the trie and the rest of the text."""
    text = text.lstrip()
    if text.startswith("te"):
        return None, text[2:]
    assert text[0] == "("
    if text.startswith("(ts "):
        key, value, rest = text[4:].split(" ", 2)
        value, _, rest = (value + " " + rest).partition(")")
        return (int(key), int(value)), rest
    assert text.startswith("(tn ")
    even, rest = parse(text[4:])
    odd, rest = parse(rest)
    assert rest.lstrip()[0] == ")"
    return [even, odd], rest.lstrip()[1:]


def find(node: object, key: int) -> int:
    """`KeyTrie.find`: the value at a key, 1 where there is none."""
    if node is None:
        return 1
    if isinstance(node, tuple):
        return node[1] if key == node[0] else 1
    return find(node[key % 2], key // 2)


def test_trie_reads_back() -> None:
    rng = np.random.default_rng(3)
    keys = rng.choice(1 << 12, size=300, replace=False).tolist()
    items = [(k, int(rng.integers(0, 70))) for k in keys]
    node, rest = parse(cc.trie(items))
    assert rest.strip() == ""
    table = dict(items)
    for key in range(1 << 12):
        assert find(node, key) == table.get(key, 1)


def test_step_matches_moves() -> None:
    block, width = "0000000001", 7
    succ = cc.successors(block, width)  # (2, P 2^w)
    for node in range(0, len(block) << width, 13):
        phase, cells = divmod(node, 1 << width)
        for free in (0, 1):
            nphase, y = cc.step(block, width, phase, cells, free)
            assert succ[free, node] == (nphase << width) + y


@pytest.mark.parametrize("block,width", [("0000000001", 12), ("01111111", 5), ("00000011", 6)])
def test_components_and_check(block: str, width: int) -> None:
    cert = cc.certificate(block, width)
    assert cc.check(cert)
    codes = cert.codes[cert.codes >= 0]  # (m,)
    ranks = codes // cert.base  # (m,)
    kept = np.array([not (cert.transient >> int(r)) & 1 for r in ranks])  # (m,)
    found, sizes = np.unique(ranks[kept], return_counts=True)
    ours = sorted((int(size), (cert.mods >> (8 * int(rank))) & 255) for rank, size in zip(found, sizes, strict=True))
    theirs = sorted((size, cycle) for size, cycle, _, both in game.component_periods(block, width))
    assert ours == theirs


def test_classes_go_past_the_game() -> None:
    # 0^9 1 at 12 cells: the game fails (one component of cyclic period 20 mixes at a phase), the classes close it.
    assert game.bad_pairs("0000000001", 12) > 0
    cert = cc.certificate("0000000001", 12)
    assert cert.base == 20 and cc.check(cert)


def test_rejects() -> None:
    with pytest.raises(ValueError):
        cc.certificate("01", 6)
    cert = cc.certificate("01111111", 5)
    top = int(np.argmax(cert.heights[4]))
    assert cert.heights[4][top] == 11
    cert.heights[4][top] = 1  # a height below that of a move from it
    assert not cc.check(cert)
    cert = cc.certificate("0000000001", 12)
    rank, label = cert.codes // cert.base, cert.codes % cert.base  # (P 2^W,), (P 2^W,)
    held = np.array([r >= 0 and not (cert.transient >> int(r)) & 1 for r in rank])  # (P 2^W,)
    node = int(np.flatnonzero(held & (cert.codes >= 0) & (label < cert.base - 1))[0])
    cert.codes[node] += 1  # one label off in a component that can hold a play
    assert not cc.check(cert)
