"""Tests of computations.c_programs: a C program compiled once against the same sum in Python, the binary reused,
several processes compiling the same program at once, and the message when no compiler is found."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import pytest

from pathlib import Path

from computations import c_programs


SOURCE = """#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    long n = atol(argv[1]), total = 0;
    for (long k = 1; k <= n; k++) total += k * k;
    printf("%ld\\n", total);
    return 0;
}
"""
ROOT = Path(__file__).resolve().parents[1]


def squares(n: int) -> int:
    """1^2 + 2^2 + ... + n^2, term by term."""
    return sum(k * k for k in range(1, n + 1))


@pytest.fixture
def probe(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """A folder with the program `probe.c`, which `compiled` reads, and a temporary directory of its own for the
    binaries, so the test builds afresh and leaves nothing behind."""
    (tmp_path / "source").mkdir()
    (tmp_path / "source" / "probe.c").write_text(SOURCE, encoding="utf-8")
    (tmp_path / "temp").mkdir(mode=0o700)
    monkeypatch.setattr(c_programs, "HERE", tmp_path / "source")
    monkeypatch.setattr("tempfile.tempdir", str(tmp_path / "temp"))
    return tmp_path


def test_compiled_against_python(probe: Path) -> None:
    """The binary sums the squares as Python does, a second request reuses it, and the build leaves only the binary in
    the folder of this user."""
    binary = c_programs.compiled.__wrapped__("probe", ("-O0", "-w"))
    for n in (0, 1, 7, 1000):
        run = subprocess.run([str(binary), str(n)], stdout=subprocess.PIPE, text=True, check=True)
        assert int(run.stdout) == squares(n)
    assert c_programs.compiled.__wrapped__("probe", ("-O0", "-w")) == binary
    assert binary.parent == c_programs.build_folder() and sorted(binary.parent.iterdir()) == [binary]
    assert c_programs.compiled.__wrapped__("probe", ("-O1", "-w")) != binary  # other flags, another binary


def test_concurrent_builds(probe: Path) -> None:
    """Four processes that compile the same program at once all get the same whole binary."""
    script = ("import sys, tempfile; from pathlib import Path; from computations import c_programs; "
              f"c_programs.HERE = Path({str(probe / 'source')!r}); tempfile.tempdir = {str(probe / 'temp')!r}; "
              "print(c_programs.compiled('probe', ('-O0', '-w')))")
    procs = [subprocess.Popen([sys.executable, "-c", script], cwd=ROOT, stdout=subprocess.PIPE, text=True,
                              env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}) for _ in range(4)]
    paths = {proc.communicate()[0].strip() for proc in procs}
    assert all(proc.returncode == 0 for proc in procs) and len(paths) == 1
    binary = Path(paths.pop())
    run = subprocess.run([str(binary), "50"], stdout=subprocess.PIPE, text=True, check=True)
    assert int(run.stdout) == squares(50) and sorted(binary.parent.iterdir()) == [binary]


def test_missing_compiler(probe: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Without `cc` or `gcc` on the path the build stops with the message the searches have always given."""
    monkeypatch.setattr(shutil, "which", lambda name: None)
    with pytest.raises(AssertionError, match="a C compiler is needed for the searches"):
        c_programs.compiled.__wrapped__("probe", ("-O0", "-w"))
