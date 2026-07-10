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
    "audits/REMEDIATION_PLAN_2026-07-10.md",
    "ForMathlib.lean",
    "ChenGeorgiouPavon2021/ProjectTheoremTargets.lean",
)

# Live status/documentation set for name-correctness ratchets. This deliberately
# EXCLUDES the historical audit and remediation plan, which may legitimately mention
# corrected or deleted names when recording resolved findings.
STATUS_DOCS = (
    "README.md",
    "STATUS.md",
    "PROOF_PIPELINE.md",
    "FOUNDATIONS.md",
    "EXTERNAL_AUDIT.md",
    "formalization.yaml",
    "LITERATURE_REFERENCES.md",
    "prose/README.md",
)

# The fully-qualified matrix-scaling theorem lives in `namespace ForMathlib`, so the
# correct name is `ForMathlib.matrix_scaling_exists`. The `.Matrix.` form is wrong.
WRONG_MATRIX_SCALING_RE = re.compile(r"ForMathlib\.Matrix\.matrix_scaling_exists")

# Continuum tautology declarations deleted in A4. They must not reappear in live status
# documents as implemented/live declarations (historical audit discussion is exempt via
# the STATUS_DOCS exclusion above).
DELETED_CONTINUUM_DECLS = (
    "dyadicNormalizedIncrementMap_generates_standardWienerRealPathMeasure",
    "cameronMartinDyadicDensity_uniformIntegrability_of_isCameronMartinPath",
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
        "## Notable reusable formalization",
        "ForMathlib.OT.dualValue_le_droValue",
        "ForMathlib.matrix_scaling_exists",
        "ForMathlib.MeasureTheory.log_integral_exp_eq_sSup",
        "AI-discovered Doeblin/weighted-average",
        "Eveson--Nussbaum",
        "## Critical vendored foundations",
        "RemyDegenne/kolmogorov_extension4",
        "mrdouglasny/gibbs-variational",
    ),
    "STATUS.md": (
        "Named capstone dependency reports",
        "Neither card inequality accepts `hge`",
        "not dependencies of",
        "two independent proof routes",
        "Doeblin/weighted-average",
        "Eveson--Nussbaum",
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


# Vendored/third-party trees whose internal prose we do not police.
EXCLUDED_PARTS = {".git", ".lake", "reference", ".reference-clones"}


def iter_documentation(root: Path):
    checker = Path(__file__).resolve()
    for path in root.rglob("*"):
        if not path.is_file() or path.suffix.lower() not in ALL_DOC_SUFFIXES:
            continue
        if EXCLUDED_PARTS.intersection(path.parts):
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

    # Name-correctness ratchets over the live status set (historical audit exempt).
    for rel in STATUS_DOCS:
        path = root / rel
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for match in WRONG_MATRIX_SCALING_RE.finditer(text):
            failures.append(
                f"{rel}:{line_number(text, match.start())}: wrong matrix-scaling name; "
                "use ForMathlib.matrix_scaling_exists (the theorem is in namespace ForMathlib)"
            )
        for name in DELETED_CONTINUUM_DECLS:
            idx = text.find(name)
            if idx >= 0:
                failures.append(
                    f"{rel}:{line_number(text, idx)}: deleted continuum declaration "
                    f"{name!r} must not appear in a live status document as an implemented "
                    "result; describe the future target in roadmap prose instead"
                )

    if failures:
        print("Documentation consistency check failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1

    print("Documentation consistency check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
