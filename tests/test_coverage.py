"""Tests of computations.coverage: the blocks excluded up to period 4 against the blocks checked directly."""

from __future__ import annotations


def test_coverage() -> None:
    """`coverage.coverage` up to period 4 against the blocks directly: both constant blocks are excluded, 001 and the
    three words of period four have traps that pass the test of reach, 01 has only a refuted one, and 011 is not reached;
    and the trap blocks by module are those of the
    Lean lists: 25 of TenTraps, 57 of ElevenTraps, 83 of TwelveTraps, 53 of ThirteenTraps, 101 of FourteenTraps, 34 of
    NaturalTraps, 1 of NaturalTrapsLarge, 70 of NaturalTrapsLong, 12 of NaturalTrapsLongLarge, 12 of FarWalls, and of
    CensusTraps13, CensusTraps14 and CensusTrapsLarge the 116, 228 and 22 that no earlier module holds, each of its
    period, 569 of CensusTraps15 and 24 of CensusTrapsLarge15, 4 of TrapPairs, the blocks of the census traps of
    MissedTraps in none, and the steered blocks are the 49 entries of the LockBlocks modules."""
    from collections import Counter
    from computations import coverage, lock_chain
    assert coverage.coverage(4) == [(1, 2, 2, 0, 0, 0, 0), (2, 1, 0, 0, 0, 1, 0), (3, 2, 0, 1, 0, 0, 1),
                                    (4, 3, 0, 3, 0, 0, 0)]
    traps = coverage.trap_blocks()
    modules = Counter(traps.values())
    assert (modules["TenTraps"], modules["ElevenTraps"], modules["TwelveTraps"]) == (25, 57, 83)
    assert (modules["ThirteenTraps"], modules["FourteenTraps"]) == (53, 101)
    assert (modules["NaturalTraps"], modules["NaturalTrapsLarge"], modules["NaturalTrapsLong"]) == (34, 1, 70)
    assert modules["FarWalls"] == 12 and all(len(b) == 12 for b, m in traps.items() if m == "FarWalls")
    assert modules["CensusTraps13"] == 116 and all(len(b) == 13 for b, m in traps.items() if m == "CensusTraps13")
    assert modules["CensusTraps14"] == 228 and all(len(b) == 14 for b, m in traps.items() if m == "CensusTraps14")
    assert modules["NaturalTrapsLongLarge"] == 12
    assert (modules["CensusTraps15"], modules["CensusTrapsLarge15"]) == (569, 24)
    assert modules["TrapPairs"] == 4 and {b for b, m in traps.items() if m == "TrapPairs"} == set(lock_chain.PAIRS)
    assert not {block for block, *_ in lock_chain.MISSED_CENSUS} & set(traps)
    assert modules["CensusTrapsLarge"] == 22 and all(len(b) in (13, 14) for b, m in traps.items()
                                                     if m == "CensusTrapsLarge")
    assert all(len(block) == {"TenTraps": 10, "ElevenTraps": 11, "TwelveTraps": 12, "ThirteenTraps": 13,
                              "FourteenTraps": 14}.get(module, len(block))
               for block, module in traps.items())
    assert "011" not in traps and len(coverage.steered_blocks()) == 49
