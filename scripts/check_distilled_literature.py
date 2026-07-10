#!/usr/bin/env python3
"""Check source maps and citation hygiene for distilled-literature notes."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

CITE_RE = re.compile(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}")
BIBITEM_RE = re.compile(r"\\bibitem\{([^}]*)\}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--notes",
        nargs="*",
        help="TeX basenames to check. By default, check every manifest entry.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo = Path(__file__).resolve().parents[1]
    lit = repo / "prose" / "distilled_literature"
    manifest_path = lit / "source_manifest.json"
    errors: list[str] = []

    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf8"))
    except Exception as ex:  # pragma: no cover - command-line diagnostic
        print(f"error: cannot read {manifest_path}: {ex}", file=sys.stderr)
        return 2

    notes = manifest.get("notes")
    if not isinstance(notes, dict):
        print("error: source_manifest.json has no object-valued 'notes' field", file=sys.stderr)
        return 2

    selected = args.notes or sorted(notes)
    for name in selected:
        meta = notes.get(name)
        if not isinstance(meta, dict):
            errors.append(f"{name}: missing manifest entry")
            continue
        path = lit / name
        if not path.is_file():
            errors.append(f"{name}: TeX file does not exist")
            continue
        text = path.read_text(encoding="utf8")

        for field in ("citation_key", "source_files", "scope", "anchors", "status"):
            if not meta.get(field):
                errors.append(f"{name}: manifest field {field!r} is empty")

        if "Source map and scope" not in text:
            errors.append(f"{name}: no visible source-map section")
        if "sourceanchor" not in text and "Source anchors" not in text:
            errors.append(f"{name}: no source anchors in TeX")
        has_bibliography = (
            "\\begin{thebibliography}" in text
            or "\\bibliography{" in text
            or "\\input{references_manual}" in text
        )
        if not has_bibliography:
            errors.append(f"{name}: no bibliography")

        cited: set[str] = set()
        for match in CITE_RE.finditer(text):
            cited.update(key.strip() for key in match.group(1).split(",") if key.strip())
        bibitems = set(BIBITEM_RE.findall(text))
        if bibitems:
            missing = sorted(cited - bibitems)
            if missing:
                errors.append(f"{name}: cited keys without local bibitems: {', '.join(missing)}")

        supplementary = meta.get("supplementary_references", [])
        if not isinstance(supplementary, list):
            errors.append(f"{name}: supplementary_references must be a list")
            supplementary = []
        for key in supplementary:
            if key not in cited:
                errors.append(f"{name}: supplementary reference {key!r} is not cited in prose")
            if bibitems and key not in bibitems:
                errors.append(f"{name}: supplementary reference {key!r} has no local bibitem")

    readme = (lit / "README.md").read_text(encoding="utf8")
    if "## Citation discipline" not in readme:
        errors.append("README.md: missing citation-discipline policy")

    if errors:
        print("Distilled-literature checks failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    print(f"Distilled-literature checks passed for {len(selected)} note(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
