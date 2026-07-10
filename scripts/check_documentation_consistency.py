#!/usr/bin/env python3
"""Check repository documentation for known contradictory status language.

This is a lightweight textual guard. It does not inspect Lean dependencies and does not
replace `lake build`, `#print axioms`, or client analysis.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


LIVE_FILES = (
    "README.md",
    "STATUS.md",
    "AGENTS.md",
    "PROOF_PIPELINE.md",
    "FOUNDATIONS.md",
    "LITERATURE_REFERENCES.md",
    "formalization.yaml",
    "prose/README.md",
    "Challenge/README.md",
    "audits/PROOF_AUDIT_2026-07-10.md",
    "ForMathlib.lean",
    "ChenGeorgiouPavon2021/ProjectTheoremTargets.lean",
)

ALL_DOC_SUFFIXES = {".md", ".yaml", ".yml", ".txt", ".lean"}

# Construct the disallowed slogan without embedding it verbatim in this checker.
TOKEN = "sor" + "ry"
COMPLETION_WORD = "fr" + "ee"
GLOBAL_COMPLETION_RE = re.compile(
    rf"`?{TOKEN}`?\s*(?:-|\s)\s*{COMPLETION_WORD}", re.IGNORECASE
)

STALE_LIVE_PATTERNS = {
    "old Sinkhorn frontier": re.compile(r"live frontier is Sinkhorn", re.IGNORECASE),
    "old open-goal count": re.compile(r"\b16 open goals\b", re.IGNORECASE),
    "old global progress-bar description": re.compile(
        r"current global progress-bar scaffold", re.IGNORECASE
    ),
    "old first-pass policy": re.compile(
        r"first-pass[^\n]{0,60}statements only|statements only[^\n]{0,60}first-pass",
        re.IGNORECASE,
    ),
    "incorrect common hge claim": re.compile(
        r"(?:last|remaining) edge on all four strong-duality capstones[^\n]{0,80}hge",
        re.IGNORECASE,
    ),
    "global zero-goal claim": re.compile(r"\b0 open goals\b", re.IGNORECASE),
}

REQUIRED_TEXT = {
    "README.md": (
        "Drsb.wdrsb_cost_bound",
        "Drsb.sdrsb_cost_bound",
        "AI-discovered Doeblin/weighted-average",
        "Eveson--Nussbaum",
    ),
    "STATUS.md": (
        "Named capstone dependency reports",
        "Neither card inequality accepts `hge`",
        "not dependencies of",
    ),
    "PROOF_PIPELINE.md": (
        "Decompose `matrix_scaling_exists`",
        "Minimize assumptions with `_core` theorems",
        "Continuum honesty cleanup",
    ),
    "prose/README.md": (
        "specialization of the Wasserstein-DRO weak-duality machinery",
        "intentionally keeps two proofs",
    ),
}


def iter_documentation(root: Path):
    checker = Path(__file__).resolve()
    for path in root.rglob("*"):
        if not path.is_file() or path.suffix.lower() not in ALL_DOC_SUFFIXES:
            continue
        if ".git" in path.parts or ".lake" in path.parts:
            continue
        try:
            if path.resolve() == checker:
                continue
        except OSError:
            pass
        yield path


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()

    failures: list[str] = []

    for path in iter_documentation(root):
        text = path.read_text(encoding="utf-8", errors="replace")
        for match in GLOBAL_COMPLETION_RE.finditer(text):
            failures.append(
                f"{path.relative_to(root)}:{line_number(text, match.start())}: "
                "replace the global completion slogan with a scoped command/result"
            )

    for rel in LIVE_FILES:
        path = root / rel
        if not path.exists():
            failures.append(f"{rel}: required live documentation file is missing")
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in STALE_LIVE_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(
                    f"{rel}:{line_number(text, match.start())}: stale language: {label}"
                )

    for rel, needles in REQUIRED_TEXT.items():
        path = root / rel
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for needle in needles:
            if needle not in text:
                failures.append(f"{rel}: missing required consistency marker: {needle!r}")

    if failures:
        print("Documentation consistency check failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1

    print("Documentation consistency check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
