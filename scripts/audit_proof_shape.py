#!/usr/bin/env python3
"""Approximate structural audit for Lean proof files and project documentation.

This intentionally does not parse Lean syntax. It scans top-level declaration starts,
measures their source spans, reports likely adapters/scaffolds, estimates local client
counts, and locates status-language patterns that should be reviewed manually.

The output is advisory. A hit is a prompt to inspect the declaration, not evidence that
it should be deleted or that its statement is mathematically weak.
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import re
import sys
from dataclasses import dataclass

DECL_RE = re.compile(
    r"^(?P<prefix>(?:private\s+|protected\s+|noncomputable\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|instance)\s+"
    r"(?P<name>[^\s:{(]+)"
)
TACTICS = (
    "simp", "simpa", "rw", "rfl", "exact", "apply", "refine", "constructor",
    "aesop", "omega", "linarith", "nlinarith", "ring", "ring_nf", "norm_num",
    "positivity", "field_simp", "convert", "ext", "funext", "by_cases", "obtain",
    "rcases", "cases", "induction", "have", "suffices", "calc",
)
TACTIC_RE = {
    tactic: re.compile(rf"(?<![A-Za-z0-9_']){re.escape(tactic)}(?![A-Za-z0-9_'])")
    for tactic in TACTICS
}
TEXT_SUFFIXES = {
    ".md", ".txt", ".yaml", ".yml", ".toml", ".lean", ".tex", ".sh", ".py"
}
# Construct these patterns without embedding the discouraged prose slogans literally.
STATUS_LANGUAGE_PATTERNS = {
    "completion slogan using free": re.compile(r"sorry" + r"[- ]?" + r"free", re.IGNORECASE),
    "completion slogan using zero": re.compile(r"zero[^\n]{0,24}`?sorry", re.IGNORECASE),
}


@dataclass(frozen=True)
class Declaration:
    path: pathlib.Path
    line: int
    end_line: int
    kind: str
    name: str
    text: str

    @property
    def span(self) -> int:
        return self.end_line - self.line + 1


@dataclass(frozen=True)
class TextFile:
    path: pathlib.Path
    text: str


def is_excluded(path: pathlib.Path) -> bool:
    excluded_parts = {".git", ".lake", ".reference-clones", "reference"}
    return bool(excluded_parts.intersection(path.parts))


def iter_lean_files(root: pathlib.Path) -> list[pathlib.Path]:
    return sorted(path for path in root.rglob("*.lean") if not is_excluded(path))


def iter_text_files(root: pathlib.Path) -> list[pathlib.Path]:
    result = []
    for path in root.rglob("*"):
        if not path.is_file() or is_excluded(path):
            continue
        if path.suffix.lower() in TEXT_SUFFIXES:
            result.append(path)
    return sorted(result)


def scan_file(root: pathlib.Path, path: pathlib.Path) -> tuple[list[str], list[Declaration]]:
    lines = path.read_text(encoding="utf8").splitlines()
    starts: list[tuple[int, re.Match[str]]] = []
    for index, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            starts.append((index, match))

    declarations: list[Declaration] = []
    for pos, (index, match) in enumerate(starts):
        end_index = starts[pos + 1][0] - 1 if pos + 1 < len(starts) else len(lines) - 1
        text = "\n".join(lines[index : end_index + 1])
        declarations.append(
            Declaration(
                path=path.relative_to(root),
                line=index + 1,
                end_line=end_index + 1,
                kind=match.group("kind"),
                name=match.group("name"),
                text=text,
            )
        )
    return lines, declarations


def common_prefix(name: str) -> str:
    parts = name.split("_")
    return "_".join(parts[: min(4, len(parts))])


def count_name_occurrences(name: str, files: list[TextFile]) -> tuple[int, list[str]]:
    pattern = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])")
    total = 0
    locations: list[str] = []
    for item in files:
        for line_number, line in enumerate(item.text.splitlines(), start=1):
            count = len(pattern.findall(line))
            if count:
                total += count
                if len(locations) < 8:
                    locations.append(f"{item.path}:{line_number}")
    return total, locations


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--min-span", type=int, default=20)
    parser.add_argument(
        "--show-clients",
        action="store_true",
        help="estimate repository-wide occurrence counts for weak/passthrough declarations",
    )
    parser.add_argument(
        "--status-language",
        action="store_true",
        help="locate documentation wording that should be replaced by scoped command/results",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    files = iter_lean_files(root)
    all_decls: list[Declaration] = []
    file_rows: list[tuple[int, int, pathlib.Path]] = []
    tactic_counts: collections.Counter[str] = collections.Counter()

    for path in files:
        lines, declarations = scan_file(root, path)
        all_decls.extend(declarations)
        file_rows.append((len(lines), len(declarations), path.relative_to(root)))
        text = "\n".join(lines)
        for tactic, pattern in TACTIC_RE.items():
            tactic_counts[tactic] += len(pattern.findall(text))

    print("Largest Lean files")
    print("lines  decls  path")
    for lines, decls, path in sorted(file_rows, reverse=True)[: args.top]:
        print(f"{lines:5d}  {decls:5d}  {path}")

    print("\nLongest top-level declaration spans (approximate)")
    print("lines  location  declaration")
    long_decls = [decl for decl in all_decls if decl.span >= args.min_span]
    for decl in sorted(long_decls, key=lambda item: item.span, reverse=True)[: args.top]:
        print(f"{decl.span:5d}  {decl.path}:{decl.line}  {decl.kind} {decl.name}")

    print("\nPotential adapters, scaffolds, or weakly encoded targets (manual review required)")
    weak_rows = []
    for decl in all_decls:
        compact = " ".join(line.strip() for line in decl.text.splitlines())
        reasons = []
        if re.search(r":\s*True\s*:=\s*by\s+trivial(?:\s|$)", compact):
            reasons.append("proves True")
        if re.search(r":=\s*by\s+exact\s+[A-Za-z0-9_'.]+(?:\s|$)", compact):
            reasons.append("direct adapter/passthrough")
        underscore_binders = len(re.findall(r"\(_h[A-Za-z0-9_]*\s*:", decl.text))
        if underscore_binders:
            reasons.append(f"{underscore_binders} explicitly unused hypothesis binder(s)")
        if reasons:
            weak_rows.append((len(reasons), decl.span, decl, "; ".join(reasons)))

    text_files: list[TextFile] = []
    if args.show_clients or args.status_language:
        text_files = [
            TextFile(path.relative_to(root), path.read_text(encoding="utf8", errors="replace"))
            for path in iter_text_files(root)
        ]

    for _score, _span, decl, reason in sorted(
        weak_rows,
        key=lambda item: (item[0], item[1], str(item[2].path), item[2].line),
        reverse=True,
    )[: args.top]:
        suffix = ""
        if args.show_clients:
            count, locations = count_name_occurrences(decl.name, text_files)
            client_estimate = max(0, count - 1)
            suffix = f"; estimated non-declaration occurrences={client_estimate}"
            if locations:
                suffix += f"; seen at {', '.join(locations)}"
        print(f"{decl.path}:{decl.line}  {decl.kind} {decl.name}  [{reason}{suffix}]")

    print("\nTactic/token concentration")
    for tactic, count in tactic_counts.most_common():
        print(f"{count:6d}  {tactic}")

    prefix_counts = collections.Counter(
        common_prefix(decl.name) for decl in all_decls if "_" in decl.name
    )
    print("\nRepeated declaration-name families (possible symmetry/API clusters)")
    for prefix, count in prefix_counts.most_common(args.top):
        if count >= 3:
            print(f"{count:5d}  {prefix}")

    if args.status_language:
        print("\nCompletion-status rhetoric candidates")
        for item in text_files:
            if item.path == pathlib.Path("scripts/audit_proof_shape.py"):
                continue
            for line_number, line in enumerate(item.text.splitlines(), start=1):
                labels = [
                    label for label, pattern in STATUS_LANGUAGE_PATTERNS.items() if pattern.search(line)
                ]
                if labels:
                    print(f"{item.path}:{line_number}  {', '.join(labels)}  {line.strip()}")

    print(
        f"\nScanned {len(files)} Lean files, {sum(row[0] for row in file_rows)} lines, "
        f"{len(all_decls)} top-level declarations.",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
