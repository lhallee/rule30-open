"""Check and build the catalog: every Lean module with its argument, every finding and every negative result.

Each entry is a Markdown file with YAML front matter. A Lean module `Rule30Open/<Dir>/<Name>.lean` has its
natural-language argument in `Rule30Open/<Dir>/<Name>.md`; findings live in `findings/<category>/`, negative results
in `negative-results/<category>/`, and `categories.yaml` lists the categories.

    python scripts/catalog.py check   # validate every entry and confirm that CATALOG.md is current
    python scripts/catalog.py write   # regenerate CATALOG.md
    python scripts/catalog.py audit   # check the axioms of every headline theorem with Lean, after `lake build`
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
import yaml

from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = ROOT / "Rule30Open"
LIBRARY_FILE = ROOT / "Rule30Open.lean"
CATALOG_FILE = ROOT / "CATALOG.md"
CATEGORIES_FILE = ROOT / "categories.yaml"
FINDINGS_ROOT = ROOT / "findings"
NEGATIVE_ROOT = ROOT / "negative-results"
NAMESPACE = "Rule30Open"

STATUSES = {"lean": ("proved",), "finding": ("paper", "computed", "conjecture"), "negative": ("negative",)}
STATUS_LABELS = {
    "proved": "proved in Lean",
    "paper": "proved on paper",
    "computed": "computed",
    "conjecture": "conjecture",
    "negative": "negative",
}
KIT_RELATIONS = ("new", "independent", "refines", "bridge")
KIT_LABELS = {
    "new": "not in the kit",
    "independent": "independent proof of a kit result",
    "refines": "extends a kit result",
    "bridge": "connects to the kit",
}
NEGATIVE_KINDS = ("no-signal", "refuted", "dead-end", "barrier")
FORMALIZATIONS = ("wanted", "partial", "not-applicable")
COMMON_FIELDS = ("title", "category", "problems", "status")
# The fields each kind of entry may carry beyond COMMON_FIELDS. Git history records who wrote what, and when.
ENTRY_FIELDS = {
    "lean": ("lean", "headline", "kit", "kit_modules", "evidence"),
    "finding": ("formalization", "evidence"),
    "negative": ("kind", "evidence"),
}
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
# What the prize's checker refuses, and the kernel bypass its replay exists to catch.
FORBIDDEN_LEAN = ("sorry", "native_decide", "decide +native", "bv_decide", "skipKernelTC")
AXIOM_DECLARATION = re.compile(r"^\s*(?:private\s+|public\s+)?axiom\s", re.MULTILINE)
FRONT_MATTER = re.compile(r"\A---\n(.*?)\n---\n", re.DOTALL)
LIBRARY_IMPORT = re.compile(r"^public import (Rule30Open\.[\w.]+)$", re.MULTILINE)
MARKDOWN_LINK = re.compile(r"\]\(([^)\s]+)\)")
AXIOMS_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS_LINE = re.compile(r"'([^']+)' does not depend on any axioms")


@dataclass(frozen=True, slots=True)
class Category:
    """One category of `categories.yaml`."""

    id: str
    title: str
    summary: str
    lean: str | None


@dataclass(frozen=True, slots=True)
class Entry:
    """One Markdown entry: its path, its kind (lean, finding or negative), its front matter and its body."""

    path: Path
    kind: str
    meta: dict[str, object]
    body: str

    @property
    def rel(self) -> str:
        return self.path.relative_to(ROOT).as_posix()

    def text(self, key: str) -> str:
        value = self.meta.get(key)
        return value if isinstance(value, str) else ""

    def names(self, key: str) -> list[str]:
        value = self.meta.get(key, [])
        return [str(item) for item in value] if isinstance(value, list) else []


def load_categories() -> list[Category]:
    raw = yaml.safe_load(CATEGORIES_FILE.read_text(encoding="utf-8"))
    return [Category(id=item["id"], title=item["title"], summary=item["summary"], lean=item.get("lean")) for item in raw]


def read_entry(path: Path, kind: str) -> Entry:
    text = path.read_text(encoding="utf-8")
    match = FRONT_MATTER.match(text)
    if match is None:
        return Entry(path=path, kind=kind, meta={}, body=text)
    meta = yaml.safe_load(match.group(1))
    if not isinstance(meta, dict):
        meta = {}
    return Entry(path=path, kind=kind, meta={str(key): value for key, value in meta.items()}, body=text[match.end():])


def lean_modules() -> list[Path]:
    return sorted(LEAN_ROOT.rglob("*.lean"))


def collect_entries() -> list[Entry]:
    entries = [read_entry(path, "lean") for path in sorted(LEAN_ROOT.rglob("*.md"))]
    entries += [read_entry(path, "finding") for path in sorted(FINDINGS_ROOT.rglob("*.md")) if path.name != "README.md"]
    entries += [read_entry(path, "negative") for path in sorted(NEGATIVE_ROOT.rglob("*.md")) if path.name != "README.md"]
    return entries


def module_name(path: Path) -> str:
    return ".".join((NAMESPACE, *path.relative_to(LEAN_ROOT).with_suffix("").parts))


def check_lean_files(categories: list[Category]) -> list[str]:
    """Pairing of modules and arguments, placement by category, the library imports, and forbidden constructs."""
    errors: list[str] = []
    lean_dirs = {category.lean for category in categories if category.lean}
    modules = lean_modules()
    for path in modules:
        rel = path.relative_to(ROOT).as_posix()
        parts = path.relative_to(LEAN_ROOT).parts
        if len(parts) != 2 or parts[0] not in lean_dirs:
            errors.append(f"{rel}: a module lives at Rule30Open/<category directory>/<Name>.lean")
        if not path.with_suffix(".md").exists():
            errors.append(f"{rel}: no argument; write {path.with_suffix('.md').relative_to(ROOT).as_posix()}")
        source = path.read_text(encoding="utf-8")
        for token in FORBIDDEN_LEAN:
            if token in source:
                errors.append(f"{rel}: contains `{token}`")
        if AXIOM_DECLARATION.search(source):
            errors.append(f"{rel}: declares an axiom")
    for path in sorted(LEAN_ROOT.rglob("*.md")):
        if not path.with_suffix(".lean").exists():
            errors.append(f"{path.relative_to(ROOT).as_posix()}: an argument without its Lean module")
    imported = set(LIBRARY_IMPORT.findall(LIBRARY_FILE.read_text(encoding="utf-8")))
    names = {module_name(path) for path in modules}
    for name in sorted(names - imported):
        errors.append(f"Rule30Open.lean: does not import {name}")
    for name in sorted(imported - names):
        errors.append(f"Rule30Open.lean: imports {name}, which does not exist")
    return errors


def declares(source: str, name: str) -> bool:
    pattern = rf"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|def|structure|abbrev)\s+{re.escape(name)}\b"
    return re.search(pattern, source, re.MULTILINE) is not None


def check_entry(entry: Entry, categories: dict[str, Category]) -> list[str]:
    """Front matter, placement and links of one entry."""
    errors = [f"{entry.rel}: missing `{key}`" for key in COMMON_FIELDS if key not in entry.meta]
    if errors:
        return errors
    allowed = {*COMMON_FIELDS, *ENTRY_FIELDS[entry.kind]}
    errors += [f"{entry.rel}: unknown field `{key}`" for key in entry.meta if key not in allowed]

    category = entry.text("category")
    if category not in categories:
        errors.append(f"{entry.rel}: unknown category `{category}`")
    if entry.text("status") not in STATUSES[entry.kind]:
        errors.append(f"{entry.rel}: status `{entry.text('status')}` is not one of {', '.join(STATUSES[entry.kind])}")
    problems = entry.meta["problems"]
    if not isinstance(problems, list) or not problems or not all(problem in (1, 2, 3) for problem in problems):
        errors.append(f"{entry.rel}: `problems` is a nonempty list drawn from 1, 2 and 3")
    heading = f"# {entry.text('title')}"
    if not entry.body.lstrip().startswith(heading + "\n"):
        errors.append(f"{entry.rel}: the body starts with the heading `{heading}`")

    if entry.kind == "lean":
        module = entry.path.with_suffix(".lean")
        expected = module_name(module)
        if entry.text("lean") != expected:
            errors.append(f"{entry.rel}: `lean` is `{expected}`")
        if category in categories and categories[category].lean != entry.path.parent.name:
            errors.append(f"{entry.rel}: category `{category}` keeps its modules in Rule30Open/{categories[category].lean}")
        headline = entry.names("headline")
        if not headline:
            errors.append(f"{entry.rel}: `headline` lists the module's main theorems")
        source = module.read_text(encoding="utf-8") if module.exists() else ""
        for name in headline:
            if not declares(source, name):
                errors.append(f"{entry.rel}: headline `{name}` is not declared in {module.name}")
        if entry.text("kit") not in KIT_RELATIONS:
            errors.append(f"{entry.rel}: `kit` is one of {', '.join(KIT_RELATIONS)}")
    else:
        root = FINDINGS_ROOT if entry.kind == "finding" else NEGATIVE_ROOT
        if entry.path.parent != root / category:
            errors.append(f"{entry.rel}: belongs in {(root / category).relative_to(ROOT).as_posix()}/")
        if entry.kind == "finding" and entry.text("formalization") not in FORMALIZATIONS:
            errors.append(f"{entry.rel}: `formalization` is one of {', '.join(FORMALIZATIONS)}")
        if entry.kind == "negative" and entry.text("kind") not in NEGATIVE_KINDS:
            errors.append(f"{entry.rel}: `kind` is one of {', '.join(NEGATIVE_KINDS)}")

    for evidence in entry.names("evidence"):
        if not (ROOT / evidence).exists():
            errors.append(f"{entry.rel}: evidence `{evidence}` does not exist")
    errors += check_links(entry.path, entry.body)
    return errors


def check_links(path: Path, body: str) -> list[str]:
    """Every relative link resolves to a file of the repository."""
    errors = []
    for target in MARKDOWN_LINK.findall(body):
        if target.startswith(("http://", "https://", "#", "mailto:")):
            continue
        resolved = (path.parent / target.split("#", 1)[0]).resolve()
        if not resolved.exists():
            errors.append(f"{path.relative_to(ROOT).as_posix()}: broken link `{target}`")
    return errors


def link(entry: Entry) -> str:
    return f"[{entry.text('title')}]({entry.rel})"


def problems_label(entry: Entry) -> str:
    problems = entry.meta.get("problems", [])
    return ", ".join(str(problem) for problem in problems) if isinstance(problems, list) else ""


def render_catalog(categories: list[Category], entries: list[Entry]) -> str:
    """CATALOG.md: a summary table, then each category's Lean results, findings and negative results."""
    by_category = {category.id: [entry for entry in entries if entry.text("category") == category.id] for category in categories}
    lean_count = sum(entry.kind == "lean" for entry in entries)
    headline_count = sum(len(entry.names("headline")) for entry in entries if entry.kind == "lean")
    finding_count = sum(entry.kind == "finding" for entry in entries)
    negative_count = sum(entry.kind == "negative" for entry in entries)
    lines = [
        "# Catalog",
        "",
        "Every result in this repository, by category. `python scripts/catalog.py write` generates this page from the",
        "front matter of the entries; edit the entries, not this page.",
        "",
        f"{lean_count} Lean modules with {headline_count} headline theorems, {finding_count} findings (proved on paper,",
        f"computed or conjectured) and {negative_count} negative results. Prize problem 1 asks whether the center column",
        "is eventually periodic, 2 whether its density of black cells tends to 1/2, and 3 whether computing its cell `n`",
        "takes effort of order `n`.",
        "",
        "| Category | Lean modules | Findings | Negative results |",
        "|---|---:|---:|---:|",
    ]
    for category in categories:
        members = by_category[category.id]
        counts = [sum(entry.kind == kind for entry in members) for kind in ("lean", "finding", "negative")]
        anchor = category.title.lower().replace(" ", "-").replace("'", "")
        lines.append(f"| [{category.title}](#{anchor}) | {counts[0]} | {counts[1]} | {counts[2]} |")
    lines += render_open_work(entries)

    for category in categories:
        members = by_category[category.id]
        lines += ["", f"## {category.title}", "", category.summary]
        lean_entries = [entry for entry in members if entry.kind == "lean"]
        findings = [entry for entry in members if entry.kind == "finding"]
        negatives = [entry for entry in members if entry.kind == "negative"]
        if lean_entries:
            lines += ["", "**Proved in Lean**", "", "| Result | Module | Headline theorems | Problems | Kit |", "|---|---|---|---|---|"]
            for entry in lean_entries:
                theorems = ", ".join(f"`{name}`" for name in entry.names("headline"))
                module = entry.text("lean").removeprefix(f"{NAMESPACE}.")
                lines.append(
                    f"| {link(entry)} | [`{module}`]({entry.path.with_suffix('.lean').relative_to(ROOT).as_posix()}) "
                    f"| {theorems} | {problems_label(entry)} | {KIT_LABELS[entry.text('kit')]} |"
                )
        if findings:
            lines += ["", "**Findings**", "", "| Result | Status | Problems | Formalization |", "|---|---|---|---|"]
            for entry in findings:
                lines.append(
                    f"| {link(entry)} | {STATUS_LABELS[entry.text('status')]} | {problems_label(entry)} "
                    f"| {entry.text('formalization').replace('-', ' ')} |"
                )
        if negatives:
            lines += ["", "**Negative results**", "", "| Result | Kind | Problems |", "|---|---|---|"]
            for entry in negatives:
                lines.append(f"| {link(entry)} | {entry.text('kind').replace('-', ' ')} | {problems_label(entry)} |")
        if not members:
            lines += ["", "Nothing yet."]
    return "\n".join(lines) + "\n"


def render_open_work(entries: list[Entry]) -> list[str]:
    """The open-work section: conjectures to settle, then findings that still want a Lean proof."""
    findings = [entry for entry in entries if entry.kind == "finding"]
    established = [entry for entry in findings if entry.text("status") != "conjecture"]
    groups = (
        ("Conjectures to prove or refute", [entry for entry in findings if entry.text("status") == "conjecture"]),
        ("Findings that want a Lean proof", [entry for entry in established if entry.text("formalization") == "wanted"]),
        ("Findings proved in Lean in part", [entry for entry in established if entry.text("formalization") == "partial"]),
    )
    lines = [
        "",
        "## Open work",
        "",
        "From the findings' front matter. Before starting in a category, read its negative results: each says where an",
        "approach stopped.",
    ]
    for title, members in groups:
        if not members:
            continue
        lines += ["", f"**{title}**", ""]
        for entry in members:
            label = problems_label(entry)
            lines.append(f"- {link(entry)}: {'problems' if ',' in label else 'problem'} {label}")
    return lines


def validate() -> tuple[list[str], list[Category], list[Entry]]:
    categories = load_categories()
    by_id = {category.id: category for category in categories}
    errors: list[str] = []
    if len(by_id) != len(categories):
        errors.append("categories.yaml: duplicate category ids")
    entries = collect_entries()
    errors += check_lean_files(categories)
    for entry in entries:
        errors += check_entry(entry, by_id)
    # PUBLIC_README.md is the repository's README.md in the published projection.
    documents = ["README.md", "PUBLIC_README.md", "CONTRIBUTING.md", "AGENTS.md", "ROADMAP.md", "computations/README.md"]
    documents += [path.relative_to(ROOT).as_posix() for path in sorted((ROOT / "literature").glob("*.md"))]
    for document in documents:
        path = ROOT / document
        if path.exists():
            errors += check_links(path, path.read_text(encoding="utf-8"))
    return errors, categories, entries


def audit(entries: list[Entry]) -> list[str]:
    """Run `#print axioms` on every headline theorem and refuse any axiom beyond the three the prize allows."""
    names = [f"{NAMESPACE}.{name}" for entry in entries if entry.kind == "lean" for name in entry.names("headline")]
    script = "import Rule30Open\n" + "".join(f"#print axioms {name}\n" for name in names)
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Audit.lean"
        path.write_text(script, encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True, check=False
        )
    output = completed.stdout + completed.stderr
    if completed.returncode != 0:
        return [f"lean failed on the audit file:\n{output}"]
    found = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()] for name, axioms in AXIOMS_LINE.findall(output)}
    found |= {name: [] for name in NO_AXIOMS_LINE.findall(output)}
    errors = [f"{name}: no axiom report" for name in names if name not in found]
    for name, axioms in sorted(found.items()):
        extra = sorted(set(axioms) - ALLOWED_AXIOMS)
        if extra:
            errors.append(f"{name}: depends on {', '.join(extra)}")
    if not errors:
        print(f"audited {len(names)} headline theorems: only {', '.join(sorted(ALLOWED_AXIOMS))}")
    return errors


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("check", "write", "audit"))
    command = parser.parse_args().command

    errors, categories, entries = validate()
    if command == "write" and not errors:
        CATALOG_FILE.write_text(render_catalog(categories, entries), encoding="utf-8", newline="\n")
        print(f"wrote {CATALOG_FILE.relative_to(ROOT).as_posix()} ({len(entries)} entries)")
    if command == "check" and not errors:
        current = CATALOG_FILE.read_text(encoding="utf-8") if CATALOG_FILE.exists() else ""
        if current != render_catalog(categories, entries):
            errors.append("CATALOG.md is out of date; run `python scripts/catalog.py write`")
        else:
            print(f"catalog current: {len(entries)} entries, {len(lean_modules())} Lean modules, each with its argument")
    if command == "audit" and not errors:
        errors = audit(entries)

    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
