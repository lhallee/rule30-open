"""The unary sandwich (findings/complexity/unary-sandwich.md): exact one-tape converters between the kit's two input
conventions, and the composite machines that carry a time bound from one convention to the other.

The kit has two one-tape models, and this module runs both exactly.

* `Rule30Problem3.Machine` reads the binary digits of n, least significant first, on the cells 0 .. l - 1 (symbol 1
  for the digit 0, 2 for the digit 1, 0 the blank; for n = 0 the tape is blank), starts in its start state with the
  head on cell 0, and halts by a transition that carries the answer. That transition is a step: the time of a run is
  the least t with `run n t = .inl answer`.
* `OneTapeGap.TM` reads 1^n on the cells 0 .. n - 1, starts in its start state with the head on cell 0, and has halted
  by step t when its state at step t is a halting state, which it never leaves; the answer is whether that state
  accepts. The time of a run is the least such t.

Two converters, written as transition tables. Each starts with the head on cell 0 and ends with a transition into
`NEXT`, the start state of the machine that runs next, with the head on cell 0 and that machine's input, and nothing
else, on the tape:

* `u2b_step`, from 1^n to the kit's input n by repeated halving: (l + 1)(2n + l + 2) steps, l the number of digits;
* `b2u_step`, from the kit's input n to 1^n by carrying the counter rightward: 2(n + 1)(l + 3) - 2 s(n) - 4 steps,
  s(n) the binary digit sum.

`unary_of_kit(M)` runs u2b and then the kit machine M, and enters a halting state where M halts: on 1^n it decides
what M computes on n in u2b(n) + t_M(n) steps. `kit_of_unary(U)` runs b2u and then the unary machine U, and halts with
U's answer one step after U reaches a halting state: on n it computes what U decides on 1^n in b2u(n) + t_U(n) + 1
steps. Here t is the exact time of a run. The composites are checked against c(n) with the quadratic simulator of
`computations.one_tape`.

    python -m computations.unary_sandwich --max-n 120 --sample 65536
"""

from __future__ import annotations

import argparse
import math
from collections.abc import Callable, Hashable
from dataclasses import dataclass
from typing import Literal

from tqdm import tqdm

from computations import one_tape
from computations.rule30 import center_column

Move = Literal[-1, 0, 1]
State = Hashable
Symbol = Hashable
Tape = dict[int, Symbol]

BLANK, D0, D1 = 0, 1, 2  # the kit's blank and its digits 0 and 1
ONE, CROSSED = "one", "crossed"  # the unary input symbol, and a one that u2b has crossed out
NEXT = "next"  # the state a converter's last transition enters: the start state of the machine that runs next


@dataclass(frozen=True)
class KitMachine:
    """A machine of the kit's binary model (`Rule30Problem3.Machine`): from `start`, `delta(state, symbol)` is
    `(answer,)`, a halt that is itself a step, or `(state, symbol, move)`."""

    start: State
    delta: Callable[[State, Symbol], tuple]


@dataclass(frozen=True)
class UnaryTM:
    """A machine of the kit's unary model (`OneTapeGap.TM`): from `start`, `delta(state, symbol)` is
    `(state, symbol, move)`; a state where `halt` is true is never left, and `accept` of it is the answer."""

    start: State
    blank: Symbol
    one: Symbol
    halt: Callable[[State], bool]
    accept: Callable[[State], bool]
    delta: Callable[[State, Symbol], tuple[State, Symbol, Move]]


def digits(n: int) -> int:
    """The number of binary digits of n, 0 for n = 0."""
    return n.bit_length()


def digit_sum(n: int) -> int:
    """The number of digits 1 of n."""
    return n.bit_count()


def binary_input(n: int) -> Tape:
    """The kit's input n (`Machine.init`): digit i of n on cell i, 1 for 0 and 2 for 1, while 2^i <= n; every other
    cell blank, so the tape is blank for n = 0. Blank cells are left out of the dictionary."""
    return {i: D1 if (n >> i) & 1 else D0 for i in range(digits(n))}


def unary_input(n: int, one: Symbol) -> Tape:
    """The unary input (`OneTapeGap.init`): `one` on the cells 0 .. n - 1, blank elsewhere."""
    return {i: one for i in range(n)}


def run_kit(machine: KitMachine, n: int, max_steps: int | None = None) -> tuple[bool, int]:
    """Run a kit machine on n: its answer and its time, the least t with `run n t = .inl answer` (the halting
    transition counts)."""
    tape, state, head, steps = binary_input(n), machine.start, 0, 0
    while max_steps is None or steps < max_steps:
        result = machine.delta(state, tape.get(head, BLANK))
        steps += 1
        if len(result) == 1:
            return bool(result[0]), steps
        state, symbol, move = result
        tape[head] = symbol
        head += move
    raise RuntimeError(f"no halt within {max_steps} steps on input {n}")


def run_unary(machine: UnaryTM, n: int, max_steps: int | None = None) -> tuple[bool, int]:
    """Run a unary machine on 1^n: its answer and its time, the least t at which its state is a halting state."""
    tape, state, head, steps = unary_input(n, machine.one), machine.start, 0, 0
    while not machine.halt(state):
        if max_steps is not None and steps >= max_steps:
            raise RuntimeError(f"no halt within {max_steps} steps on input {n}")
        state, symbol, move = machine.delta(state, tape.get(head, machine.blank))
        tape[head] = symbol
        head += move
        steps += 1
    return bool(machine.accept(state)), steps


# Unary to binary. A cell of the unary region holds ONE or CROSSED; once an output digit d has been written on it, it
# holds the pair (ONE, d) or (CROSSED, d). Pass k crosses out the first, third, fifth, ... of the remaining ones, so
# that floor(n / 2^(k + 1)) remain, and writes their parity floor(n / 2^k) mod 2, digit k of n, on cell k.

U2B_START = ("scan", 0, 0)


def unary_part(symbol: Symbol) -> Symbol:
    """ONE or CROSSED for a cell of the unary region, with or without an output digit; the symbol itself otherwise."""
    return symbol[0] if isinstance(symbol, tuple) else symbol


def u2b_step(state: tuple, symbol: Symbol) -> tuple[State, Symbol, Move]:
    """The table of u2b. States: ('scan', p, seen) walks right over the unary region, p the parity of the ones met so
    far and seen whether there was one; ('back', d) walks left to the blank before cell 0 with the digit d;
    ('slot', d) walks right over the cells that carry digits and writes d on the first that does not; ('back2',)
    walks left again; ('clean',) walks left from the end of the region and leaves the kit's digits on the cells that
    carry them and blanks elsewhere."""
    phase = state[0]
    if phase == "scan":
        _, parity, seen = state
        if symbol == BLANK:  # the cell after the region: a pass with no one left ends the conversion
            return (("back", parity) if seen else ("clean",)), BLANK, -1
        if unary_part(symbol) == ONE:
            if parity == 0:  # cross out the first, third, fifth, ... remaining one
                crossed = (CROSSED, symbol[1]) if isinstance(symbol, tuple) else CROSSED
                return ("scan", 1, 1), crossed, 1
            return ("scan", 0, 1), symbol, 1
        return state, symbol, 1  # a crossed cell
    if phase == "back":
        if symbol == BLANK:
            return ("slot", state[1]), BLANK, 1
        return state, symbol, -1
    if phase == "slot":
        if isinstance(symbol, tuple):
            return state, symbol, 1
        if symbol in (ONE, CROSSED):
            return ("back2",), (symbol, state[1]), -1
        raise ValueError(f"u2b: no transition from {state} on {symbol!r}")  # cell k < l <= n is in the region
    if phase == "back2":
        if symbol == BLANK:
            return U2B_START, BLANK, 1
        return state, symbol, -1
    if phase == "clean":
        if symbol == BLANK:  # the blank before cell 0: hand over on cell 0
            return NEXT, BLANK, 1
        if isinstance(symbol, tuple):
            return state, D1 if symbol[1] else D0, -1
        return state, BLANK, -1
    raise ValueError(f"u2b: unknown state {state}")


# Binary to unary. The counter, l cells, least significant digit first, starts on the cells 0 .. l - 1. Each round
# subtracts one, then moves the counter one cell right and leaves a ONE on the cell it vacates; when the counter is
# zero, it is erased and the head returns to cell 0.

B2U_START = ("dec",)


def b2u_step(state: tuple, symbol: Symbol) -> tuple[State, Symbol, Move]:
    """The table of b2u. States: ('dec',) subtracts one (zeros become ones up to the lowest one, which becomes zero;
    the blank after the counter means it was zero); ('lsb',) walks left to the cell before the counter; ('pick',)
    takes the lowest digit and leaves a ONE; ('shift', d) carries each digit one cell right; ('ret',) walks left to the
    last ONE and steps onto the counter; ('erase',) blanks the spent counter; ('home',) walks left over the ones to
    the blank before cell 0."""
    phase = state[0]
    if phase == "dec":
        if symbol == D0:
            return state, D1, 1
        if symbol == D1:
            return ("lsb",), D0, -1
        if symbol == BLANK:
            return ("erase",), BLANK, -1
    elif phase == "lsb":
        if symbol in (D0, D1):
            return state, symbol, -1
        if symbol in (ONE, BLANK):
            return ("pick",), symbol, 1
    elif phase == "pick":
        if symbol in (D0, D1):
            return ("shift", symbol), ONE, 1
    elif phase == "shift":
        if symbol in (D0, D1):
            return ("shift", symbol), state[1], 1
        if symbol == BLANK:
            return ("ret",), state[1], -1
    elif phase == "ret":
        if symbol in (D0, D1):
            return state, symbol, -1
        if symbol == ONE:
            return B2U_START, ONE, 1
    elif phase == "erase":
        if symbol in (D0, D1):
            return state, BLANK, -1
        if symbol == ONE:
            return ("home",), ONE, -1
        if symbol == BLANK:  # n = 0: the counter was empty
            return NEXT, BLANK, 1
    elif phase == "home":
        if symbol == ONE:
            return state, ONE, -1
        if symbol == BLANK:
            return NEXT, BLANK, 1
    raise ValueError(f"b2u: no transition from {state} on {symbol!r}")


def u2b_time(n: int) -> int:
    """The exact time of u2b: (l + 1)(2n + l + 2) = 2n(l + 1) + l^2 + 3l + 2."""
    ell = digits(n)
    return (ell + 1) * (2 * n + ell + 2)


def b2u_time(n: int) -> int:
    """The exact time of b2u: 2(n + 1)(l + 3) - 2 s(n) - 4, which is 2nl + 6n - 2 s(n) + 2l + 2 for n >= 1 and 2 for
    n = 0."""
    ell = digits(n)
    return 2 * (n + 1) * (ell + 3) - 2 * digit_sum(n) - 4


def u2b_pass_times(n: int) -> list[int]:
    """The time of each pass of u2b by the proof: 2n + 2k + 4 for the pass k = 0 .. l - 1 that writes digit k, and
    2n + 2 for the last pass with the clean-up."""
    return [2 * n + 2 * k + 4 for k in range(digits(n))] + [2 * n + 2]


def b2u_round_times(n: int) -> list[int]:
    """The time of each round of b2u by the proof: 2 tz(v) + 2l + 3 for the round that turns v into v - 1, v = n
    .. 1 (tz the trailing zeros), and n + 2l + 2 for the round that finds the counter zero, with the erasure and the
    walk home (2 for n = 0)."""
    ell = digits(n)
    rounds = [2 * ((v & -v).bit_length() - 1) + 2 * ell + 3 for v in range(n, 0, -1)]
    return rounds + [n + 2 * ell + 2]


def convert(kind: Literal["u2b", "b2u"], n: int) -> tuple[list[int], Tape, int]:
    """Run one converter alone on its input for n up to its transition into NEXT: the steps of each pass (u2b) or
    round (b2u), a new one starting at each transition into the start state from another state, the tape without its
    blanks, and the head. The transition into NEXT counts as a step of the last pass or round."""
    if kind == "u2b":
        step, start, tape = u2b_step, U2B_START, unary_input(n, ONE)
    else:
        step, start, tape = b2u_step, B2U_START, binary_input(n)
    state, head, counts = start, 0, [0]
    while state != NEXT:
        nxt, symbol, move = step(state, tape.get(head, BLANK))
        tape[head] = symbol
        head += move
        counts[-1] += 1
        if nxt == start and state != start:
            counts.append(0)
        state = nxt
    return counts, {i: s for i, s in tape.items() if s != BLANK}, head


def halts(state: State) -> bool:
    """The halting states of the unary machines here: ('halt', answer)."""
    return state[0] == "halt"


def answer(state: State) -> bool:
    """Whether a halting state ('halt', answer) accepts."""
    return state[0] == "halt" and bool(state[1])


def kit_symbol(symbol: Symbol) -> Symbol:
    """What the kit machine of `unary_of_kit` reads: its own symbols, and the blank for the symbols of u2b, which are
    gone from the tape when it starts."""
    return symbol if isinstance(symbol, int) else BLANK


def unary_of_kit(machine: KitMachine) -> UnaryTM:
    """u2b, then the kit machine: a unary machine with the states ('u2b', s), ('kit', p) and the halting states
    ('halt', b), the kit's blank as its blank and ONE as its input symbol. Where the kit machine halts with b, it
    enters ('halt', b), so a run of t steps of the kit machine is t steps here."""

    def delta(state: State, symbol: Symbol) -> tuple[State, Symbol, Move]:
        tag, inner = state
        if tag == "u2b":
            nxt, out, move = u2b_step(inner, symbol)
            return (("kit", machine.start) if nxt == NEXT else ("u2b", nxt)), out, move
        if tag == "kit":
            result = machine.delta(inner, kit_symbol(symbol))
            if len(result) == 1:
                return ("halt", bool(result[0])), symbol, 0
            nxt, out, move = result
            return ("kit", nxt), out, move
        return state, symbol, 0  # a halting state; `run_unary` never steps it, as `OneTapeGap.step` keeps it

    return UnaryTM(start=("u2b", U2B_START), blank=BLANK, one=ONE, halt=halts, accept=answer, delta=delta)


def kit_of_unary(machine: UnaryTM) -> KitMachine:
    """b2u, then the unary machine: a kit machine with the states ('b2u', s) and ('tm', q). The unary machine's
    symbols are written as ('tm', x) and read back by `decode`, which also reads the kit's blank as its blank and ONE
    as its input symbol; in a halting state of the unary machine the kit machine halts with its answer, one step
    more."""

    def decode(symbol: Symbol) -> Symbol:
        if isinstance(symbol, tuple) and symbol[0] == "tm":
            return symbol[1]
        return machine.one if symbol == ONE else machine.blank  # the digits are gone from the tape when it starts

    def delta(state: State, symbol: Symbol) -> tuple:
        tag, inner = state
        if tag == "b2u":
            nxt, out, move = b2u_step(inner, symbol)
            return (("tm", machine.start) if nxt == NEXT else ("b2u", nxt)), out, move
        if machine.halt(inner):
            return (machine.accept(inner),)
        nxt, out, move = machine.delta(inner, decode(symbol))
        return ("tm", nxt), ("tm", out), move

    return KitMachine(start=("b2u", B2U_START), delta=delta)


def low_bit(state: State, symbol: Symbol) -> tuple[bool]:
    """The kit's `lowBit`: halt at once with whether cell 0 holds the digit 1."""
    return (symbol == D1,)


SIMULATOR = KitMachine(start=one_tape.State("init0"), delta=one_tape.transition)
LOW_BIT = KitMachine(start=0, delta=low_bit)


def periodic_tm(f: Callable[[int], bool], first: int, period: int) -> UnaryTM:
    """The kit's `OneTapeGap.periodicTM`: for f with period `period` from `first`, count the ones with a counter that
    wraps from first + period back to first, and at the blank halt with f of the count; it decides f in n + 1
    steps."""

    def wrap(count: int) -> int:
        return count + 1 if count + 1 < first + period else first

    def delta(state: State, symbol: Symbol) -> tuple[State, Symbol, Move]:
        tag, value = state
        if tag == "count":
            return (("count", wrap(value)), True, 1) if symbol else (("halt", bool(f(value))), False, 1)
        return state, symbol, 1

    return UnaryTM(start=("count", 0), blank=False, one=True, halt=halts, accept=answer, delta=delta)


def check_composites(max_n: int) -> None:
    """For n <= max_n: the unary machine (u2b, then the simulator) decides c(n) in u2b(n) + time(n) steps, and the
    binary machine made of it (b2u, then that unary machine) computes c(n) in b2u(n) + u2b(n) + time(n) + 1 steps,
    time(n) the simulator's exact time; each converter leaves exactly the other convention's input."""
    column = center_column(max_n + 1)  # (max_n + 1,)
    unary = unary_of_kit(SIMULATOR)
    binary = kit_of_unary(unary)
    for n in tqdm(range(max_n + 1), desc="composites", leave=False):
        counts, tape, head = convert("u2b", n)
        assert tape == binary_input(n) and head == 0 and counts == u2b_pass_times(n), n
        counts, tape, head = convert("b2u", n)
        assert tape == unary_input(n, ONE) and head == 0 and counts == b2u_round_times(n), n
        assert sum(u2b_pass_times(n)) == u2b_time(n) and sum(b2u_round_times(n)) == b2u_time(n), n
        answer, steps = run_unary(unary, n)
        assert answer == bool(column[n]) and steps == u2b_time(n) + one_tape.time(n), (n, steps)
        answer, steps = run_kit(binary, n)
        assert answer == bool(column[n]) and steps == b2u_time(n) + u2b_time(n) + one_tape.time(n) + 1, (n, steps)


def sample_points(limit: int) -> list[int]:
    """n = 4^j - 1, 4^j, 4^j + 1 for 4 <= 4^j <= limit."""
    points, power = [], 4
    while power <= limit:
        points += [power - 1, power, power + 1]
        power *= 4
    return points


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-n", type=int, default=120, help="check the composites for every n up to this")
    parser.add_argument("--sample", type=int, default=65536,
                        help="run the converters at 4^j - 1, 4^j, 4^j + 1 up to this")
    args = parser.parse_args()
    check_composites(args.max_n)
    print(f"every n <= {args.max_n}: u2b and b2u take exactly (l + 1)(2n + l + 2) and 2(n + 1)(l + 3) - 2s(n) - 4"
          " steps and leave the other input; u2b + simulator decides c(n) in u2b(n) + time(n) steps, and b2u + that"
          " machine computes c(n) in b2u(n) + u2b(n) + time(n) + 1 steps")
    print("       n   l   u2b steps   u2b/(n log2 n)   u2b/((n+1)(l+1))   b2u steps   b2u/(n log2 n)"
          "   b2u/((n+1)(l+1))")
    for n in tqdm(sample_points(args.sample), desc="converters", leave=False):
        u2b_counts, tape, head = convert("u2b", n)
        assert tape == binary_input(n) and head == 0 and u2b_counts == u2b_pass_times(n), n
        b2u_counts, tape, head = convert("b2u", n)
        assert tape == unary_input(n, ONE) and head == 0 and b2u_counts == b2u_round_times(n), n
        u2b, b2u = sum(u2b_counts), sum(b2u_counts)
        assert u2b == u2b_time(n) and b2u == b2u_time(n), n
        scale, box = n * math.log2(n), (n + 1) * (digits(n) + 1)
        tqdm.write(f"{n:8d} {digits(n):3d} {u2b:11d} {u2b / scale:16.3f} {u2b / box:18.3f}"
                   f" {b2u:11d} {b2u / scale:16.3f} {b2u / box:18.3f}")
    print("every pass and round, and every total, equals its closed form")


if __name__ == "__main__":
    main()
