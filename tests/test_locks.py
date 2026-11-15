"""Tests of computations.locks: locked nodes, predecessors and mixed nodes against forward searches over the game's
list of moves."""

from __future__ import annotations

import numpy as np

from computations import game
from computations.rule30 import distinct


def forward_moves(source: np.ndarray, target: np.ndarray, nodes: int) -> np.ndarray:
    """The two targets of each node, read from the game's list of moves: row v holds the targets of the moves from v."""
    # source, target: (2 p n,)
    order = np.argsort(source, kind="stable")  # (2 p n,)
    assert (np.bincount(source, minlength=nodes) == 2).all()
    return target[order].reshape(nodes, 2)  # (p n, 2)


def forward_reach(moves: np.ndarray, node: int) -> np.ndarray:
    """The nodes that some walk along the moves (`forward_moves`) reaches from `node`, the node itself among them: a
    forward breadth-first search that steps only the nodes found in the round before."""
    # moves: (p n, 2)
    seen = np.zeros(moves.shape[0], dtype=bool)  # (p n,)
    seen[node] = True
    frontier = np.array([node])  # (f,)
    while frontier.size:
        after = moves[frontier].reshape(-1)  # (2 f,)
        frontier = np.unique(after[~seen[after]])  # (f,), each new node once
        seen[frontier] = True
    return seen  # (p n,)


def test_locks() -> None:
    """`locks.lock_info` against forward searches: for sampled nodes of the games of 0111 at width 13 and 01010101011 at
    width 10, a node is locked exactly when the nodes it reaches show one value of the left column at each phase, and it
    reaches a locked node exactly when `lock_info` says so; 0111 at width 13 is steerable and 0001 is not. `steering`
    against Rule 30 run on all windows at once: its sequence leaves every start at a listed window that is locked."""
    from computations import locks
    assert locks.steerable("0111", 13) and not locks.steerable("0001", 13)
    rng = np.random.default_rng(11)
    for block, width in (("0111", 13), ("01010101011", 10)):
        source, target, _, _, column = game.game_graph(block, width)  # (2 p n,), (2 p n,), _, _, (p n,)
        locked, reach = locks.lock_info(block, width)  # (p n,), (p n,)
        nodes = column.size
        phase = np.arange(nodes) >> width  # (p n,)
        moves = forward_moves(source, target, nodes)  # (p n, 2)
        for node in rng.integers(0, nodes, 6).tolist():
            seen = forward_reach(moves, node)  # (p n,)
            both = any(column[seen & (phase == ph)].any() and (~column[seen & (phase == ph)]).any()
                       for ph in range(len(block)))
            assert locked[node] == (not both)
            assert reach[node] == bool((seen & locked).any())
    # the steering sequence of 0111, run on every window by bit operations: each ends at a listed locked window
    width, period = 13, 4
    values, finals = locks.steering("0111", width)
    locked, _ = locks.lock_info("0111", width)  # (p n,)
    mask = (1 << width) - 1
    for start in range(period):
        windows = np.arange(1 << width, dtype=np.int64)  # (2^W,), bit j is cell j + 1 right of the column
        for step, value in enumerate(values):
            left = ((windows << 1) | int("0111"[(start + step) % period])) & mask  # (2^W,)
            right = (windows >> 1) | (value << (width - 1))  # (2^W,)
            windows = left ^ (windows | right)  # (2^W,)
        final = (start + len(values)) % period
        assert set(distinct(windows).tolist()) <= set(finals[final])
        assert locked[(final << width) + windows].all()
    assert locks.longest_run("0111") == 3 and locks.longest_run("01010101011") == 2 and locks.longest_run("1000001") == 5
    # no locked node for 01 at width 8: from every node a forward search meets both values of the left column at a phase
    source, target, _, _, column = game.game_graph("01", 8)  # (2 p n,), (2 p n,), _, _, (p n,)
    phase = np.arange(column.size) >> 8  # (p n,)
    moves = forward_moves(source, target, column.size)  # (p n, 2)
    reached = np.eye(column.size, dtype=np.float32)  # (p n, p n), row v: the nodes found from v
    reached[np.arange(column.size)[:, None], moves] = 1.0
    while True:  # walks of up to twice the length each round, until no row grows
        longer = (reached @ reached > 0).astype(np.float32)  # (p n, p n)
        if (longer == reached).all():
            break
        reached = longer
    assert (reached[:: 37] > 0).tolist() == [forward_reach(moves, node).tolist() for node in range(0, column.size, 37)]
    for seen in reached > 0:  # (p n,) each
        assert any(column[seen & (phase == ph)].any() and (~column[seen & (phase == ph)]).any() for ph in range(2))
    assert not locks.has_lock("01", 8) and locks.has_lock("0111", 13)
    assert locks.family("0^k 11101", 3) == "00011101" and locks.family("00 1^k 01", 4) == "00111101"
    assert locks.fewest_mixed("0111", 13) == 0 and locks.fewest_mixed("01", 8) == 1
    assert locks.lock_census([2, 4], [13]) == {(2, 13): [], (4, 13): ["0111"]}
    # white alone: 27 white values in column 8 lock every window of 7 cells beside 000011111111, and 26 do not
    block, width = "000011111111", 7
    assert locks.constant_steering(block, width, 0) == 27 and locks.white_run(block, [6, 7, 8]) == (7, 27)
    locked, _ = locks.lock_info(block, width)  # (p n,)
    mask, period, ends = (1 << width) - 1, len(block), {}
    for start in range(period):
        windows = np.arange(1 << width, dtype=np.int64)  # (2^W,)
        for step in range(27):
            left = ((windows << 1) | int(block[(start + step) % period])) & mask  # (2^W,)
            windows = left ^ (windows | (windows >> 1))  # (2^W,), the free cell white
            ends[(start, step + 1)] = locked[(((start + step + 1) % period) << width) + windows].all()
    assert all(ends[(start, 27)] for start in range(period))
    assert not all(ends[(start, 26)] for start in range(period))


def test_mixed_nodes() -> None:
    """`locks.mixed_nodes`, found backward by predecessor arithmetic, against `locks.lock_info`, found along the game's
    list of moves: the same locked nodes for blocks with locks (0111 and 00011101 at 13 cells) and without (001011,
    alone and repeated, at 13 cells); the 2,611 locked nodes of 0001 at 16 cells; and no locked node for 001011 at 13
    cells modulo 12, at 15 modulo 6, or for any block of period 6 at 11 cells modulo 12 (`lock_census`)."""
    from computations import locks
    for block, width in (("0111", 13), ("00011101", 13), ("001011", 13), ("001011001011", 13)):
        locked, _ = locks.lock_info(block, width)  # (p n,)
        assert (locked == ~locks.mixed_nodes(block, width)).all()
        assert locks.has_lock(block, width, wide=True) == bool(locked.any())
    locked = locks.locked_nodes("0001", 16)  # (p n,), the locked nodes of `lock_info` without its search for reach
    assert (locked == ~locks.mixed_nodes("0001", 16)).all() and int(locked.sum()) == 2611
    assert locks.lock_census([6], [11], repeat=2, wide=True) == {(6, 11): []}
    assert not locks.has_lock("001011", 15, wide=True)


def test_predecessors() -> None:
    """`locks.predecessors` lists exactly the nodes with a move to each node, against the moves of `game.moves` at
    small widths and at 13 cells, which it reads in two pieces (`locks.CHUNK`), and `lock_chain.successors` gives
    those moves; `reach_nodes` agrees with `locks.back_closure` over `game.moves`."""
    from computations import game, lock_chain, locks

    assert locks.CHUNK < 13
    for word, width, every in (("001", 5, 7), ("0001011", 6, 7), ("0010111", 4, 7), ("0001011", 13, 997)):
        source, target = game.moves(word, width)  # (2 p n,), (2 p n,)
        nodes = np.arange(len(word) << width, dtype=np.uint64)  # (p n,)
        after = lock_chain.successors(word, width, nodes)  # (2, p n)
        assert sorted(zip(source.tolist(), target.tolist(), strict=True)) == sorted(
            zip(np.tile(nodes, 2).tolist(), after.reshape(-1).tolist(), strict=True))
        for node in range(0, len(word) << width, every):
            want = sorted(set(source[target == node].tolist()))
            got = sorted(set(locks.predecessors(word, width, np.array([node], dtype=np.uint64)).tolist()))
            assert got == want
    t = {"word": "0001011", "cells": 6, "states": [(0, 5), (3, 17), (9, 40)]}
    for width in (4, 6, 8):
        source, target = game.moves("0001011", width)
        dense = locks.back_closure(lock_chain.trap_nodes((t,), width), source, target)  # (p n,)
        assert (lock_chain.reach_nodes((t,), width) == dense).all()
