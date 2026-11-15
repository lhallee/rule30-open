"""The C programs beside the modules, compiled once and kept for later processes.

`compiled` builds `computations/<name>.c` with the given flags, or reuses the binary that an earlier process built from
the same source, compiler and flags on the same machine. Binaries are kept under a hash of all four in a folder that
only this user can write: on Unix, `rule30-open-<uid>` in the temporary directory, checked to be this user's and closed
to others; on Windows, `rule30-open` in the user's own temporary directory. Each build goes to a fresh directory and is
then renamed into place, so processes that compile at the same time never run half a binary.
"""

from __future__ import annotations

import functools
import hashlib
import os
import platform
import shutil
import subprocess
import sys
import tempfile

from pathlib import Path


HERE = Path(__file__).resolve().parent
SUFFIX = ".exe" if sys.platform == "win32" else ""  # Windows runs a program only by its full name


def build_folder() -> Path:
    """The folder that keeps the binaries of this user."""
    if sys.platform == "win32":
        folder = Path(tempfile.gettempdir()) / "rule30-open"  # the temporary directory of a Windows user is their own
        folder.mkdir(exist_ok=True)
        return folder

    folder = Path(tempfile.gettempdir()) / f"rule30-open-{os.getuid()}"
    folder.mkdir(mode=0o700, exist_ok=True)
    if folder.stat().st_uid != os.getuid() or folder.stat().st_mode & 0o022:
        return Path(tempfile.mkdtemp(prefix="c_programs_"))  # not ours alone, so compile afresh

    return folder


@functools.cache
def compiled(name: str, flags: tuple[str, ...]) -> Path:
    """Compile computations/<name>.c with `flags`, or reuse the binary an earlier process compiled from the same source
    with the same compiler and flags on the same machine."""
    cc = shutil.which("cc") or shutil.which("gcc")
    assert cc, "a C compiler is needed for the searches"
    source = HERE / f"{name}.c"
    command = [cc, *flags, str(source)]
    key = hashlib.sha256(source.read_bytes() + repr((command, platform.node(), platform.machine())).encode())
    folder = build_folder()
    out = folder / f"{name}-{key.hexdigest()[:20]}{SUFFIX}"
    if out.exists():
        return out

    fresh = Path(tempfile.mkdtemp(prefix="c_programs_", dir=folder)) / f"{name}{SUFFIX}"
    subprocess.run([*command, "-o", str(fresh)], check=True)
    try:
        os.replace(fresh, out)  # whole, so a process running at the same time never sees half a binary
    except PermissionError:
        # Windows refuses to replace a binary that is running; another process built the same one first.
        assert out.exists(), f"could not move {fresh} to {out}"
        fresh.unlink()

    fresh.parent.rmdir()
    return out
