#!/usr/bin/env python3
"""Fail on tautological `True`-shaped theorem scaffolds and ignored `True` binders.

This is a narrow **textual** guard for agent-authored scaffolding. It is NOT a Lean
parser: it does not elaborate terms, resolve `True` through definitions, or understand
tactic blocks. It only matches two syntactic shapes that have repeatedly slipped in as
placeholder theorems and then read as if they carried mathematical content:

  1. a theorem/lemma whose conclusion is literally `True`, discharged by `trivial`
     (a tautological scaffold — it proves nothing);
  2. an ignored hypothesis of the form `(_h... : True)` or `(h... : True)` in a
     production theorem signature (a binder that reserves an argument slot for a fact
     that is never stated).

It deliberately does NOT reject every occurrence of the token `True`: `def`s,
`structure`/`class` fields, `example`s, comments, logical lemmas, and challenge
specifications may legitimately mention `True`. The matcher is aimed only at the two
theorem-shaped tautology patterns above.

Use accurately stated interfaces or roadmap prose instead of a `True`-valued stand-in.

Exit status is nonzero if any production hit is found.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Directories excluded from the production scan.
EXCLUDED_PARTS = {".git", ".lake", "reference", ".reference-clones", "Challenge"}

# Explicit, intentionally EMPTY allowlist. A genuinely intentional future exception
# must be added here WITH a documenting comment (file + reason), so that silently
# weakening the check is impossible. Entries are "path:decl_or_binder" strings.
ALLOWLIST: frozenset[str] = frozenset()

# A theorem/lemma whose conclusion is `True`, proved by `trivial`. `\s` spans newlines,
# so this catches the common `: True := by\n  trivial` multiline formatting. `True`
# immediately before the definitional `:=` identifies the *conclusion* (a hypothesis
# `(_h : True)` is followed by `)`, not `:=`), so this does not fire on binders.
TAUTOLOGY_RE = re.compile(r":\s*True\s*:=\s*by\s+trivial\b")

# The declaration keyword + name immediately preceding a signature.
DECL_RE = re.compile(
    r"(?:^|\n)[ \t]*"
    r"(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*"
    r"(?P<kind>theorem|lemma)\s+(?P<name>[^\s:{(]+)"
)

# An ignored `True` binder: `(_hui : True)` or `(hfoo : True)`.
TRUE_BINDER_RE = re.compile(r"\(\s*(?P<binder>_?h\w*)\s*:\s*True\s*\)")


def is_excluded(path: Path) -> bool:
    return bool(EXCLUDED_PARTS.intersection(path.parts))


def iter_lean_files(root: Path):
    for path in root.rglob("*.lean"):
        if path.is_file() and not is_excluded(path):
            yield path


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def declarations(text: str):
    """Yield (name, start, end) spans for each top-level theorem/lemma."""
    starts = [(m.start(), m.group("name")) for m in DECL_RE.finditer(text)]
    for i, (start, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        yield name, start, end


def scan_file(path: Path, root: Path) -> list[str]:
    text = path.read_text(encoding="utf-8", errors="replace")
    rel = path.relative_to(root)
    failures: list[str] = []

    for name, start, end in declarations(text):
        block = text[start:end]

        # (1) Tautological `: True := by trivial` scaffold.
        m = TAUTOLOGY_RE.search(block)
        if m:
            key = f"{rel}:{name}"
            if key not in ALLOWLIST:
                line = line_number(text, start + m.start())
                failures.append(
                    f"{rel}:~{line}: tautological-True-scaffold in `{name}` "
                    f"(conclusion `True`, proved by `trivial`) — state an accurate "
                    f"interface or move the target to roadmap prose instead"
                )

        # (2) Ignored `True` binder, searched only in the signature (before `:=`).
        sig_end = block.find(":=")
        signature = block if sig_end < 0 else block[:sig_end]
        for bm in TRUE_BINDER_RE.finditer(signature):
            binder = bm.group("binder")
            key = f"{rel}:{name}:{binder}"
            if key in ALLOWLIST:
                continue
            line = line_number(text, start + bm.start())
            failures.append(
                f"{rel}:~{line}: ignored-True-binder `({binder} : True)` in `{name}` "
                f"— replace the placeholder slot with the fact it stands for, or "
                f"remove it and describe the obligation in roadmap prose"
            )

    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    args = parser.parse_args()
    root = args.root.resolve()

    failures: list[str] = []
    for path in iter_lean_files(root):
        failures.extend(scan_file(path, root))

    if failures:
        print("Non-vacuous scaffold check failed:", file=sys.stderr)
        for failure in sorted(failures):
            print(f"- {failure}", file=sys.stderr)
        return 1

    print("Non-vacuous scaffold check passed (no True-shaped scaffolds or binders).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
