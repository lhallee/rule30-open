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
import os
import re
import subprocess
import sys
import tempfile
import yaml

from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Literal


ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = "Rule30Open"
LIBRARY_FILE = "Rule30Open.lean"
CATALOG_FILE = "CATALOG.md"
CATEGORIES_FILE = "categories.yaml"
FINDINGS_DIR = "findings"
NEGATIVE_DIR = "negative-results"
# The Markdown files outside the entries whose links `check` follows; .lake and other hidden directories stay out.
DOCUMENT_GLOBS = ("*.md", "computations/*.md", "literature/*.md", "tests/*.md", "findings/README.md",
                  "negative-results/README.md")
NAMESPACE = "Rule30Open"

Kind = Literal["lean", "finding", "negative"]
STATUSES: dict[Kind, tuple[str, ...]] = {
    "lean": ("proved",),
    "finding": ("paper", "computed", "conjecture"),
    "negative": ("negative",),
}
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
FORMALIZATIONS = ("wanted", "partial", "kit", "not-applicable")
FORMALIZATION_LABELS = {"wanted": "wanted", "partial": "partial", "kit": "proved in the kit",
                        "not-applicable": "not applicable"}
PROBLEMS = (1, 2, 3)
COMMON_FIELDS = ("title", "category", "problems", "status")
# The fields each kind of entry may carry beyond COMMON_FIELDS. Git history records who wrote what, and when.
ENTRY_FIELDS: dict[Kind, tuple[str, ...]] = {
    "lean": ("lean", "headline", "kit", "kit_modules", "evidence"),
    "finding": ("formalization", "evidence"),
    "negative": ("kind", "evidence"),
}
TEXT_FIELDS = ("title", "category", "status", "lean", "kit", "formalization", "kind")
LIST_FIELDS = ("headline", "kit_modules", "evidence")
CATEGORY_FIELDS = ("id", "title", "summary")
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
# What the prize's checker refuses, and the kernel bypass its replay exists to catch.
FORBIDDEN_LEAN = ("sorry", "native_decide", "decide +native", "bv_decide", "skipKernelTC")
AXIOM_DECLARATION = re.compile(r"^\s*(?:private\s+|public\s+)?axiom\s", re.MULTILINE)
# A declaration at the start of a line, matched after a newline rather than at `^`: the literal `\n` lets the regex
# engine skip ahead, five times faster over the 96 MB of Lean source than trying `^` at every character.
DECLARATION = re.compile(r"\n\s*(?:@\[[^\]]*\]\s*)?(?:theorem|def|structure|abbrev)\s+([^\s(){}\[\]:]+)")
NAMESPACE_LINE = re.compile(r"\n\s*namespace\s+(\S+)")
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
    """One Markdown entry: its path, its path from the repository root, its kind, its front matter and its body."""

    path: Path
    rel: str
    kind: Kind
    meta: dict[str, object]
    body: str

    def text(self, key: str) -> str:
        value = self.meta.get(key, "")
        assert isinstance(value, str), f"{self.rel}: `{key}` was not checked as text"
        return value

    def names(self, key: str) -> list[str]:
        value = self.meta.get(key, [])
        assert isinstance(value, list), f"{self.rel}: `{key}` was not checked as a list"
        return [str(item) for item in value]


@dataclass(frozen=True, slots=True)
class LeanModule:
    """What `check` needs from one Lean source, read once: its declared names, the dot-separated parts of its
    `namespace` lines, and the constructs it must not use."""

    declared: frozenset[str]
    namespace_parts: frozenset[str]
    forbidden: tuple[str, ...]
    declares_axiom: bool


def posix_sorted(paths: Iterable[Path]) -> list[Path]:
    """Paths in case-sensitive POSIX order, part by part, as `sorted` orders them on Linux, so the catalog comes out
    the same on every platform (Windows paths compare without case)."""
    return sorted(paths, key=lambda path: path.as_posix().split("/"))


def relative(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def load_categories(root: Path) -> tuple[list[Category], list[str]]:
    """The categories in file order, or the errors that make `categories.yaml` unusable."""
    try:
        raw = yaml.safe_load((root / CATEGORIES_FILE).read_text(encoding="utf-8"))
    except yaml.YAMLError as error:
        return [], [f"{CATEGORIES_FILE}: not valid YAML{yaml_location(error, 1)}: {yaml_problem(error)}"]
    if not isinstance(raw, list):
        return [], [f"{CATEGORIES_FILE}: a list of categories, each starting `- id: <id>`"]

    categories: list[Category] = []
    errors: list[str] = []
    for number, item in enumerate(raw, start=1):
        if not isinstance(item, dict):
            errors.append(f"{CATEGORIES_FILE}: category {number} is not a mapping; write `- id: <id>`, then `title:`, "
                          "`summary:` and, if it has Lean modules, `lean:`")
            continue
        label = f"category {number} (`{item['id']}`)" if isinstance(item.get("id"), str) else f"category {number}"
        missing = [key for key in CATEGORY_FIELDS if not isinstance(item.get(key), str)]
        errors += [f"{CATEGORIES_FILE}: {label} has no `{key}` as text; add `{key}: ...`" for key in missing]
        errors += [f"{CATEGORIES_FILE}: {label} has the unknown field `{key}`; the fields are id, title, summary, lean"
                   for key in item if key not in (*CATEGORY_FIELDS, "lean")]
        lean = item.get("lean")
        if lean is not None and not isinstance(lean, str):
            errors.append(f"{CATEGORIES_FILE}: {label}: `lean` is the name of a directory under {LEAN_DIR}/")
        if not missing and (lean is None or isinstance(lean, str)):
            categories.append(Category(id=item["id"], title=item["title"], summary=item["summary"], lean=lean))
    ids = [category.id for category in categories]
    errors += [f"{CATEGORIES_FILE}: the id `{id_}` appears {ids.count(id_)} times; give each category its own id"
               for id_ in sorted(set(ids)) if ids.count(id_) > 1]
    return categories, errors


def yaml_location(error: yaml.YAMLError, first_line: int) -> str:
    """` at line n` of the file for an error whose YAML text starts at line `first_line` of that file."""
    if isinstance(error, yaml.MarkedYAMLError) and error.problem_mark is not None:
        return f" at line {error.problem_mark.line + first_line}"
    return ""


def yaml_problem(error: yaml.YAMLError) -> str:
    return error.problem if isinstance(error, yaml.MarkedYAMLError) and error.problem else str(error)


def read_entry(path: Path, kind: Kind, root: Path) -> Entry | str:
    """The entry at `path`, or the one-line error that says why its front matter cannot be read."""
    rel = relative(path, root)
    text = path.read_text(encoding="utf-8")
    match = FRONT_MATTER.match(text)
    if match is None:
        return (f"{rel}: no front matter; start the file with a line `---`, then the fields "
                f"({', '.join((*COMMON_FIELDS, *ENTRY_FIELDS[kind]))}), then a line `---`")
    try:
        meta = yaml.safe_load(match.group(1))
    except yaml.YAMLError as error:
        return (f"{rel}: the front matter is not valid YAML{yaml_location(error, 2)}: {yaml_problem(error)}; put a value "
                "that holds `: ` or starts with a character such as `*`, `&`, `[` or `{` in quotes, as in "
                "`title: \"A: B\"`")
    if not isinstance(meta, dict):
        return f"{rel}: the front matter is not a set of fields; write one `field: value` per line"
    return Entry(path=path, rel=rel, kind=kind, meta={str(key): value for key, value in meta.items()},
                 body=text[match.end():])


def collect_entries(root: Path, lean_arguments: list[Path]) -> tuple[list[Entry], list[str]]:
    """Every entry in catalog order (Lean arguments, findings, negative results), and the entries that cannot be read."""
    paths: list[tuple[Path, Kind]] = [(path, "lean") for path in lean_arguments]
    for directory, kind in ((FINDINGS_DIR, "finding"), (NEGATIVE_DIR, "negative")):
        paths += [(path, kind) for path in posix_sorted((root / directory).rglob("*.md")) if path.name != "README.md"]
    entries: list[Entry] = []
    errors: list[str] = []
    for path, kind in paths:
        entry = read_entry(path, kind, root)
        if isinstance(entry, str):
            errors.append(entry)
        else:
            entries.append(entry)
    return entries, errors


def module_name(path: Path, root: Path) -> str:
    return ".".join((NAMESPACE, *path.relative_to(root / LEAN_DIR).with_suffix("").parts))


def read_lean_module(path: Path) -> LeanModule:
    source = path.read_text(encoding="utf-8")
    return LeanModule(
        declared=frozenset(DECLARATION.findall("\n" + source)),
        namespace_parts=frozenset(part for line in NAMESPACE_LINE.findall("\n" + source) for part in line.split(".")),
        forbidden=tuple(token for token in FORBIDDEN_LEAN if token in source),
        declares_axiom="axiom" in source and AXIOM_DECLARATION.search(source) is not None,
    )


def check_lean_files(root: Path, categories: list[Category], modules: dict[Path, LeanModule],
                     arguments: list[Path]) -> list[str]:
    """Pairing of modules and arguments, placement by category, the library imports, and forbidden constructs."""
    errors: list[str] = []
    lean_root = root / LEAN_DIR
    lean_dirs = {category.lean for category in categories if category.lean}
    argument_set = set(arguments)
    for path, module in modules.items():
        rel = relative(path, root)
        parts = path.relative_to(lean_root).parts
        if len(parts) != 2 or parts[0] not in lean_dirs:
            errors.append(f"{rel}: a module lives at {LEAN_DIR}/<category directory>/<Name>.lean")
        if path.with_suffix(".md") not in argument_set:
            errors.append(f"{rel}: no argument; write {relative(path.with_suffix('.md'), root)}")
        errors += [f"{rel}: contains `{token}`" for token in module.forbidden]
        if module.declares_axiom:
            errors.append(f"{rel}: declares an axiom")
    errors += [f"{relative(path, root)}: an argument without its Lean module" for path in arguments
               if path.with_suffix(".lean") not in modules]
    imported = set(LIBRARY_IMPORT.findall((root / LIBRARY_FILE).read_text(encoding="utf-8")))
    names = {module_name(path, root) for path in modules}
    errors += [f"{LIBRARY_FILE}: does not import {name}" for name in sorted(names - imported)]
    errors += [f"{LIBRARY_FILE}: imports {name}, which does not exist" for name in sorted(imported - names)]
    return errors


def check_types(entry: Entry) -> list[str]:
    """Each known field has its type: text, a list of text, or `problems` as a list of distinct problem numbers."""
    errors: list[str] = []
    for key in TEXT_FIELDS:
        if key in entry.meta and not isinstance(entry.meta[key], str):
            errors.append(f"{entry.rel}: `{key}` is text; put its value in quotes, as in `{key}: \"...\"`")
    for key in LIST_FIELDS:
        value = entry.meta.get(key, [])
        if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
            errors.append(f"{entry.rel}: `{key}` is a list of names in brackets, as in `{key}: [first, second]`, "
                          "even for one name")
    problems = entry.meta["problems"]
    valid = isinstance(problems, list) and problems and all(
        isinstance(problem, int) and not isinstance(problem, bool) and problem in PROBLEMS for problem in problems
    )
    if not valid:
        errors.append(f"{entry.rel}: `problems` is a nonempty list drawn from 1, 2 and 3, as in `problems: [1, 3]`")
    elif len(set(problems)) != len(problems):
        repeated = sorted({problem for problem in problems if problems.count(problem) > 1})
        errors.append(f"{entry.rel}: `problems` lists {', '.join(map(str, repeated))} more than once; list each "
                      "problem once")
    return errors


def declares(module: LeanModule, name: str) -> bool:
    """Whether `module` declares `name`, directly or, for a dotted `P.q`, as `q` inside namespaces that spell `P`.

    The dotted case is conservative: `q` must be declared and every dot-separated part of `P` must be a part of some
    `namespace` line of the file.
    """
    if name in module.declared:
        return True
    prefix, _, last = name.rpartition(".")
    return bool(prefix) and last in module.declared and all(part in module.namespace_parts
                                                            for part in prefix.split("."))


def missing_field(entry: Entry, key: str) -> str:
    hints = {
        "title": "the claim, as the catalog will show it",
        "category": "one of the ids in categories.yaml",
        "problems": "the prize problems it bears on, as in [1, 3]",
        "status": f"one of {', '.join(STATUSES[entry.kind])}",
    }
    return f"{entry.rel}: missing `{key}`; add the line `{key}: ...` with {hints[key]}"


def check_entry(entry: Entry, root: Path, categories: dict[str, Category], modules: dict[Path, LeanModule],
                exists: dict[str, bool]) -> list[str]:
    """Front matter, placement and links of one entry."""
    errors = [missing_field(entry, key) for key in COMMON_FIELDS if key not in entry.meta]
    if errors:
        return errors
    allowed = {*COMMON_FIELDS, *ENTRY_FIELDS[entry.kind]}
    errors += [f"{entry.rel}: unknown field `{key}`; the fields of this kind of entry are {', '.join(sorted(allowed))}"
               for key in entry.meta if key not in allowed]
    type_errors = check_types(entry)
    if type_errors:
        return errors + type_errors

    category = entry.text("category")
    if category not in categories:
        errors.append(f"{entry.rel}: unknown category `{category}`; use one of the ids in {CATEGORIES_FILE}: "
                      f"{', '.join(categories)}")
    if entry.text("status") not in STATUSES[entry.kind]:
        errors.append(f"{entry.rel}: status `{entry.text('status')}` is not one of {', '.join(STATUSES[entry.kind])}")
    heading = f"# {entry.text('title')}"
    if not entry.body.lstrip().startswith(heading + "\n"):
        errors.append(f"{entry.rel}: the body starts with the heading `{heading}`")

    if entry.kind == "lean":
        module_path = entry.path.with_suffix(".lean")
        expected = module_name(module_path, root)
        if entry.text("lean") != expected:
            errors.append(f"{entry.rel}: `lean` is `{expected}`")
        if category in categories and categories[category].lean != entry.path.parent.name:
            errors.append(f"{entry.rel}: category `{category}` keeps its modules in {LEAN_DIR}/{categories[category].lean}")
        headline = entry.names("headline")
        if not headline:
            errors.append(f"{entry.rel}: `headline` lists the module's main theorems")
        module = modules.get(module_path)
        if module is not None:
            errors += [f"{entry.rel}: headline `{name}` is not declared in {module_path.name}" for name in headline
                       if not declares(module, name)]
        if entry.text("kit") not in KIT_RELATIONS:
            errors.append(f"{entry.rel}: `kit` is one of {', '.join(KIT_RELATIONS)}")
    else:
        directory = FINDINGS_DIR if entry.kind == "finding" else NEGATIVE_DIR
        if category in categories and entry.path.parent != root / directory / category:
            errors.append(f"{entry.rel}: belongs in {directory}/{category}/")
        if entry.kind == "finding" and entry.text("formalization") not in FORMALIZATIONS:
            errors.append(f"{entry.rel}: `formalization` is one of {', '.join(FORMALIZATIONS)}")
        if entry.kind == "negative" and entry.text("kind") not in NEGATIVE_KINDS:
            errors.append(f"{entry.rel}: `kind` is one of {', '.join(NEGATIVE_KINDS)}")

    errors += [f"{entry.rel}: evidence `{evidence}` does not exist" for evidence in entry.names("evidence")
               if not path_exists(os.path.join(root, evidence), exists)]
    errors += check_links(entry.path, entry.rel, entry.body, exists)
    return errors


def path_exists(path: str, exists: dict[str, bool]) -> bool:
    """`os.path.exists` of the normalized path, asked of the file system once per path."""
    key = os.path.normpath(path)
    if key not in exists:
        exists[key] = os.path.exists(key)
    return exists[key]


def check_links(path: Path, rel: str, body: str, exists: dict[str, bool]) -> list[str]:
    """Every relative link resolves to a file of the repository."""
    errors: list[str] = []
    for target in MARKDOWN_LINK.findall(body):
        if target.startswith(("http://", "https://", "#", "mailto:")):
            continue
        if not path_exists(os.path.join(path.parent, target.split("#", 1)[0]), exists):
            errors.append(f"{rel}: broken link `{target}`")
    return errors


def link(entry: Entry) -> str:
    return f"[{entry.text('title')}]({entry.rel})"


def problems_label(entry: Entry) -> str:
    problems = entry.meta["problems"]
    assert isinstance(problems, list), f"{entry.rel}: `problems` was not checked as a list"
    return ", ".join(str(problem) for problem in problems)


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
                    f"| {link(entry)} | [`{module}`]({entry.rel.removesuffix('.md')}.lean) "
                    f"| {theorems} | {problems_label(entry)} | {KIT_LABELS[entry.text('kit')]} |"
                )
        if findings:
            lines += ["", "**Findings**", "", "| Result | Status | Problems | Formalization |", "|---|---|---|---|"]
            for entry in findings:
                lines.append(
                    f"| {link(entry)} | {STATUS_LABELS[entry.text('status')]} | {problems_label(entry)} "
                    f"| {FORMALIZATION_LABELS[entry.text('formalization')]} |"
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


@dataclass(frozen=True, slots=True)
class Validation:
    """The outcome of `validate`: the errors, and the categories and entries to render when there are none."""

    errors: list[str]
    categories: list[Category]
    entries: list[Entry]
    module_count: int


def validate(root: Path) -> Validation:
    categories, errors = load_categories(root)
    if errors:
        return Validation(errors=errors, categories=categories, entries=[], module_count=0)
    by_id = {category.id: category for category in categories}
    lean_root = root / LEAN_DIR
    modules = {path: read_lean_module(path) for path in posix_sorted(lean_root.rglob("*.lean"))}
    arguments = posix_sorted(lean_root.rglob("*.md"))
    entries, errors = collect_entries(root, arguments)
    errors += check_lean_files(root, categories, modules, arguments)
    exists: dict[str, bool] = {}
    for entry in entries:
        errors += check_entry(entry, root, by_id, modules, exists)
    for path in posix_sorted({path for pattern in DOCUMENT_GLOBS for path in root.glob(pattern)}):
        errors += check_links(path, relative(path, root), path.read_text(encoding="utf-8"), exists)
    return Validation(errors=errors, categories=categories, entries=entries, module_count=len(modules))


def audit(root: Path, entries: list[Entry]) -> list[str]:
    """Run `#print axioms` on every headline theorem and refuse any axiom beyond the three the prize allows."""
    names = [f"{NAMESPACE}.{name}" for entry in entries if entry.kind == "lean" for name in entry.names("headline")]
    script = "import Rule30Open\n" + "".join(f"#print axioms {name}\n" for name in names)
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Audit.lean"
        path.write_text(script, encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=root, capture_output=True, text=True, check=False
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


def run(command: str, root: Path) -> list[str]:
    """Run one command on the repository at `root` and return its errors."""
    validation = validate(root)
    if validation.errors:
        return validation.errors
    catalog_path = root / CATALOG_FILE
    rendered = render_catalog(validation.categories, validation.entries)
    if command == "write":
        catalog_path.write_text(rendered, encoding="utf-8", newline="\n")
        print(f"wrote {CATALOG_FILE} ({len(validation.entries)} entries)")
        return []
    if command == "check":
        current = catalog_path.read_text(encoding="utf-8") if catalog_path.exists() else ""
        if current != rendered:
            return [f"{CATALOG_FILE} is out of date; run `python scripts/catalog.py write`"]
        print(f"catalog current: {len(validation.entries)} entries, {validation.module_count} Lean modules, each with its "
              "argument")
        return []
    assert command == "audit", command
    return audit(root, validation.entries)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("check", "write", "audit"))
    errors = run(parser.parse_args().command, ROOT)
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
