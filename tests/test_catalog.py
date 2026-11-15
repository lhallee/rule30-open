"""`scripts/catalog.py` on small repositories built in a temporary directory, one malformed entry or category at a time,
so each message names its file and says what to write, and on this repository, whose catalog `check` passes and `write`
leaves unchanged. Paths sort in case-sensitive POSIX order, so the catalog is the same on Windows and Linux."""

from __future__ import annotations

import importlib.util
import sys

from pathlib import Path
from types import ModuleType


ROOT = Path(__file__).resolve().parents[1]
CATEGORIES = "- id: seeds\n  title: Seeds\n  lean: Seeds\n  summary: Initial rows.\n"
FINDING = "title: T\ncategory: seeds\nproblems: [1]\nstatus: paper\nformalization: wanted\n"


def load_catalog() -> ModuleType:
    """scripts/catalog.py as a module; `scripts` is not a package."""
    spec = importlib.util.spec_from_file_location("catalog", ROOT / "scripts" / "catalog.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["catalog"] = module  # dataclasses look their module up while the class body runs
    spec.loader.exec_module(module)
    return module


catalog = load_catalog()


def repository(root: Path, finding: str | None = FINDING, categories: str = CATEGORIES) -> Path:
    """A repository with one category, one Lean module with its argument, and one finding whose front matter, between
    its `---` lines, is `finding` (no front matter when `finding` is None)."""
    (root / "Rule30Open" / "Seeds").mkdir(parents=True)
    (root / "findings" / "seeds").mkdir(parents=True)
    (root / "negative-results").mkdir()
    (root / "categories.yaml").write_text(categories, encoding="utf-8")
    (root / "Rule30Open.lean").write_text("module\n\npublic import Rule30Open.Seeds.Seed\n", encoding="utf-8")
    (root / "Rule30Open" / "Seeds" / "Seed.lean").write_text("module\n\ntheorem seed_main : True := trivial\n",
                                                             encoding="utf-8")
    (root / "Rule30Open" / "Seeds" / "Seed.md").write_text(
        "---\ntitle: S\ncategory: seeds\nproblems: [1]\nstatus: proved\nlean: Rule30Open.Seeds.Seed\n"
        "headline: [seed_main]\nkit: new\n---\n\n# S\n", encoding="utf-8")
    front = "" if finding is None else f"---\n{finding}---\n\n"
    (root / "findings" / "seeds" / "x.md").write_text(f"{front}# T\n\nBody.\n", encoding="utf-8")
    return root


def errors(root: Path) -> list[str]:
    return catalog.validate(root).errors


def test_well_formed(tmp_path: Path) -> None:
    """The small repository passes, `write` makes its catalog, and `check` then finds it current."""
    root = repository(tmp_path)
    assert errors(root) == []
    assert catalog.run("check", root) == ["CATALOG.md is out of date; run `python scripts/catalog.py write`"]
    assert catalog.run("write", root) == []
    assert catalog.run("check", root) == []
    assert "| [S](Rule30Open/Seeds/Seed.md) | [`Seeds.Seed`](Rule30Open/Seeds/Seed.lean) | `seed_main` | 1 |" in (
        root / "CATALOG.md").read_text(encoding="utf-8")


def test_unquoted_colon(tmp_path: Path) -> None:
    root = repository(tmp_path, FINDING.replace("title: T", "title: A: B"))
    assert errors(root) == [
        "findings/seeds/x.md: the front matter is not valid YAML at line 2: mapping values are not allowed here; put a "
        "value that holds `: ` or starts with a character such as `*`, `&`, `[` or `{` in quotes, as in "
        "`title: \"A: B\"`"
    ]


def test_no_front_matter(tmp_path: Path) -> None:
    root = repository(tmp_path, None)
    assert errors(root) == [
        "findings/seeds/x.md: no front matter; start the file with a line `---`, then the fields (title, category, "
        "problems, status, formalization, evidence), then a line `---`"
    ]


def test_front_matter_not_fields(tmp_path: Path) -> None:
    root = repository(tmp_path, "just a sentence\n")
    assert errors(root) == [
        "findings/seeds/x.md: the front matter is not a set of fields; write one `field: value` per line"
    ]


def test_missing_field(tmp_path: Path) -> None:
    root = repository(tmp_path, FINDING.replace("status: paper\n", ""))
    assert errors(root) == [
        "findings/seeds/x.md: missing `status`; add the line `status: ...` with one of paper, computed, conjecture"
    ]


def test_unknown_category(tmp_path: Path) -> None:
    """One line, with the ids to choose from, and no second line about where the entry belongs."""
    root = repository(tmp_path, FINDING.replace("category: seeds", "category: nope"))
    assert errors(root) == ["findings/seeds/x.md: unknown category `nope`; use one of the ids in categories.yaml: seeds"]


def test_misplaced_finding(tmp_path: Path) -> None:
    root = repository(tmp_path, FINDING.replace("category: seeds", "category: columns"),
                      CATEGORIES + "- id: columns\n  title: Columns\n  summary: Columns.\n")
    assert errors(root) == ["findings/seeds/x.md: belongs in findings/columns/"]


def test_category_without_summary(tmp_path: Path) -> None:
    root = repository(tmp_path, categories="- id: seeds\n  title: Seeds\n  lean: Seeds\n")
    assert errors(root) == ["categories.yaml: category 1 (`seeds`) has no `summary` as text; add `summary: ...`"]


def test_duplicate_category(tmp_path: Path) -> None:
    root = repository(tmp_path, categories=CATEGORIES * 2)
    assert errors(root) == ["categories.yaml: the id `seeds` appears 2 times; give each category its own id"]


def test_scalar_for_list(tmp_path: Path) -> None:
    """`evidence: computations/x.py` is a string, not a list of one path."""
    root = repository(tmp_path, FINDING + "evidence: computations/x.py\n")
    assert errors(root) == [
        "findings/seeds/x.md: `evidence` is a list of names in brackets, as in `evidence: [first, second]`, even for "
        "one name"
    ]


def test_duplicate_problems(tmp_path: Path) -> None:
    root = repository(tmp_path, FINDING.replace("problems: [1]", "problems: [1, 3, 1]"))
    assert errors(root) == ["findings/seeds/x.md: `problems` lists 1 more than once; list each problem once"]


def test_problems_out_of_range(tmp_path: Path) -> None:
    root = repository(tmp_path, FINDING.replace("problems: [1]", "problems: [true]"))
    assert errors(root) == [
        "findings/seeds/x.md: `problems` is a nonempty list drawn from 1, 2 and 3, as in `problems: [1, 3]`"
    ]


def test_title_not_text(tmp_path: Path) -> None:
    root = repository(tmp_path, FINDING.replace("title: T", "title: 2026"))
    assert errors(root) == ["findings/seeds/x.md: `title` is text; put its value in quotes, as in `title: \"...\"`"]


def test_headline_not_declared(tmp_path: Path) -> None:
    """A headline theorem matches a declared name exactly: `seed` is not `seed_main`."""
    root = repository(tmp_path)
    argument = root / "Rule30Open" / "Seeds" / "Seed.md"
    argument.write_text(argument.read_text(encoding="utf-8").replace("[seed_main]", "[seed_main, seed]"),
                        encoding="utf-8")
    assert errors(root) == ["Rule30Open/Seeds/Seed.md: headline `seed` is not declared in Seed.lean"]


def test_dotted_headline(tmp_path: Path) -> None:
    """A dotted headline `P.q` is declared as `q` inside namespaces whose lines spell every part of `P`, on one
    `namespace` line or nested over several; a part that no `namespace` line holds, or an undeclared `q`, is refused."""
    root = repository(tmp_path)
    module = root / "Rule30Open" / "Seeds" / "Seed.lean"
    argument = root / "Rule30Open" / "Seeds" / "Seed.md"
    argument.write_text(argument.read_text(encoding="utf-8").replace(
        "[seed_main]", "[seed_main, Frames.Seed.inner, Frames.Seed.absent, Other.inner]"), encoding="utf-8")
    module.write_text("module\n\ntheorem seed_main : True := trivial\n\nnamespace Rule30Open.Frames\nnamespace Seed\n\n"
                      "theorem inner : True := trivial\n\nend Seed\nend Rule30Open.Frames\n", encoding="utf-8")
    assert errors(root) == [
        "Rule30Open/Seeds/Seed.md: headline `Frames.Seed.absent` is not declared in Seed.lean",
        "Rule30Open/Seeds/Seed.md: headline `Other.inner` is not declared in Seed.lean",
    ]


def test_declares(tmp_path: Path) -> None:
    """`declares` on a module read from source: a direct name, a name spelled with its namespace, and the refusals,
    among them a dotted declaration asked for by its last part alone."""
    path = tmp_path / "Module.lean"
    path.write_text("module\n\n@[simp] theorem Top.direct : True := trivial\nnamespace A.B\ndef q : Nat := 0\nend A.B\n",
                    encoding="utf-8")
    module = catalog.read_lean_module(path)
    assert catalog.declares(module, "Top.direct")
    assert catalog.declares(module, "q")
    assert catalog.declares(module, "A.B.q")
    assert catalog.declares(module, "B.q")
    assert not catalog.declares(module, "C.q")
    assert not catalog.declares(module, "A.B.r")
    assert not catalog.declares(module, "direct")


def test_forbidden_lean(tmp_path: Path) -> None:
    root = repository(tmp_path)
    (root / "Rule30Open" / "Seeds" / "Seed.lean").write_text(
        "module\n\ntheorem seed_main : True := by sorry\naxiom extra : False\n", encoding="utf-8")
    assert errors(root) == ["Rule30Open/Seeds/Seed.lean: contains `sorry`", "Rule30Open/Seeds/Seed.lean: declares an axiom"]


def test_broken_link(tmp_path: Path) -> None:
    root = repository(tmp_path)
    (root / "README.md").write_text("See [the notes](notes.md) and [the seeds](findings/seeds/x.md#t).\n",
                                    encoding="utf-8")
    assert errors(root) == ["README.md: broken link `notes.md`"]


def test_posix_order() -> None:
    """Case-sensitive, part by part, on every platform: `TrapSets` before `Traps001` because `S` precedes `s`, and a
    directory before a longer name that starts with it."""
    paths = [Path("Columns/Traps001.md"), Path("Columns/TrapSets.md"), Path("a-b/z.md"), Path("a/y.md")]
    assert [path.as_posix() for path in catalog.posix_sorted(paths)] == [
        "Columns/TrapSets.md", "Columns/Traps001.md", "a/y.md", "a-b/z.md"
    ]


def test_repository() -> None:
    """`check` passes on this repository and `write` would leave CATALOG.md as it is, byte for byte."""
    validation = catalog.validate(ROOT)
    assert validation.errors == []
    rendered = catalog.render_catalog(validation.categories, validation.entries)
    assert (ROOT / "CATALOG.md").read_bytes() == rendered.encode("utf-8")
