#!/usr/bin/env python3
"""Pre-flight signature check for the challenge comparator.

The comparator exports the challenge (`Conformance`) and solution (`Leaderboard`)
declarations with `lean4export` and compares them **without alpha-normalizing
universe parameters or the instance telescope**.  So a conformance can `lake
build` green, be `#print axioms`-clean, and *still* fail with `statement do not
match` — the two documented classes being a shifted universe slot (an added or
reordered `variable`, since unused type variables reserve slots) and a missing
instance in the binder telescope.

This script reproduces the journal's cheap local proxy for that export check,
for every theorem named in each comparator config:

  1. `#print <thm>` in each module, compared on the raw `.{…}` universe
     signature — `#print` shows the positional universe list the exporter sees;
     `#check` alpha-normalizes it away, so it cannot catch a slot shift.
  2. `set_option pp.all true in #check @<thm>` in each module, compared on the
     full type (all binders + instances explicit) — this catches telescope /
     body drift, which the universe signature alone does not.

Both must match for a theorem to pass.  Empty Lean output is treated as an
error, never a pass (two empty captures diff as "identical").

The real comparator (with landrun) remains ground truth; this only tells you,
cheaply, whether it is worth running.

Usage:
  python3 scripts/check_comparator_signatures.py                       # all comparator/*.json
  python3 scripts/check_comparator_signatures.py comparator/candidate-01-gram-rigidity.json ...
  python3 scripts/check_comparator_signatures.py --no-build            # assume modules already built

Exit status is nonzero if any theorem mismatches or errors.

See dev/journals/comparator-statement-export-matching-2026-06-14.md.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tempfile


def git_root() -> str:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        )
        return out.stdout.strip()
    except subprocess.CalledProcessError:
        return os.getcwd()


def module_to_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def run_lean(snippet: str) -> str:
    """Run a one-off Lean snippet in the project env; return combined output."""
    fd, path = tempfile.mkstemp(suffix=".lean")
    try:
        with os.fdopen(fd, "w", encoding="utf8") as f:
            f.write(snippet + "\n")
        proc = subprocess.run(
            ["lake", "env", "lean", path],
            capture_output=True, text=True, timeout=600,
        )
        return (proc.stdout or "") + (proc.stderr or "")
    except subprocess.TimeoutExpired:
        return "<lean timed out>"
    finally:
        os.unlink(path)


def universe_sig(module: str, theorem: str) -> tuple[str | None, str]:
    """Raw positional universe signature from `#print` (the exporter's view)."""
    out = run_lean(f"import {module}\n#print {theorem}")
    if not out.strip():
        return None, out
    # `theorem Foo.Bar.baz.{u_1, u_2, u_4} : …`  — capture the `.{…}` (or none).
    m = re.search(re.escape(theorem) + r"(\.\{[^}]*\})", out)
    if m:
        return m.group(1), out
    # Theorem printed but with no universe params, or not found at all.
    # NB: `\b` cannot be used here — a Lean name may end in `'` (a non-word char),
    # and `\b` never matches between `'` and the following space, so primed
    # theorems would be misreported as "no usable output".
    if re.search(r"(?:theorem|def|lemma)\s+" + re.escape(theorem) + r"(?![\w'])", out):
        return "(no universes)", out
    return None, out


def full_type(module: str, theorem: str) -> tuple[str | None, str]:
    """Fully-explicit type from `pp.all #check` (binders + instances explicit)."""
    out = run_lean(f"import {module}\nset_option pp.all true in\n#check @{theorem}")
    if not out.strip():
        return None, out
    anchor = "@" + theorem
    start = out.find(anchor)
    if start < 0:
        return None, out
    colon = out.find(" : ", start)
    if colon < 0:
        return None, out
    typ = re.sub(r"\s+", " ", out[colon + 3:]).strip()
    return (typ or None), out


def check_theorem(challenge: str, solution: str, theorem: str) -> tuple[str, list[str]]:
    """Return (status, detail-lines) for one theorem. status in PASS/FAIL/ERROR."""
    detail: list[str] = []

    sig_sol, raw_sol = universe_sig(solution, theorem)
    sig_conf, raw_conf = universe_sig(challenge, theorem)
    typ_sol, tout_sol = full_type(solution, theorem)
    typ_conf, tout_conf = full_type(challenge, theorem)

    def bad(label: str, out: str) -> None:
        detail.append(f"    {label}: no usable output — Lean said:")
        for line in out.strip().splitlines()[:6]:
            detail.append(f"      {line}")

    if sig_sol is None:
        bad(f"#print in solution module {solution}", raw_sol)
    if sig_conf is None:
        bad(f"#print in challenge module {challenge}", raw_conf)
    if typ_sol is None:
        bad(f"pp.all #check in solution module {solution}", tout_sol)
    if typ_conf is None:
        bad(f"pp.all #check in challenge module {challenge}", tout_conf)
    if None in (sig_sol, sig_conf, typ_sol, typ_conf):
        return "ERROR", detail

    ok = True
    if sig_sol != sig_conf:
        ok = False
        detail.append("    universe signature MISMATCH (the export check will reject):")
        detail.append(f"      solution   : {theorem}{sig_sol}")
        detail.append(f"      conformance: {theorem}{sig_conf}")
        detail.append("      → mirror the source's `variable` order in the Conformance "
                      "(unused type vars reserve slots).")
    if typ_sol != typ_conf:
        ok = False
        detail.append("    full type MISMATCH (binder telescope / body differs):")
        detail.append(f"      solution   : {typ_sol}")
        detail.append(f"      conformance: {typ_conf}")
    return ("PASS" if ok else "FAIL"), detail


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("configs", nargs="*", help="comparator config JSONs (default: comparator/*.json)")
    ap.add_argument("--no-build", action="store_true",
                    help="skip `lake build` of the modules (assume already built)")
    args = ap.parse_args()

    root = git_root()
    os.chdir(root)

    configs = args.configs or sorted(glob.glob("comparator/*.json"))
    if not configs:
        print("no comparator configs found", file=sys.stderr)
        return 2

    rows: list[tuple[str, str, str]] = []  # (status, theorem, config)
    overall = 0

    for config in configs:
        if not os.path.isfile(config):
            print(f"error: config not found: {config}", file=sys.stderr)
            overall = 2
            continue
        with open(config, encoding="utf8") as f:
            data = json.load(f)
        challenge = data["challenge_module"]
        solution = data["solution_module"]
        theorems = data["theorem_names"]

        print("=" * 70)
        print(f"Config:    {config}")
        print(f"Challenge: {challenge}")
        print(f"Solution:  {solution}")
        print("=" * 70)

        if not args.no_build:
            print(f"Building {challenge} and {solution} …")
            b = subprocess.run(["lake", "build", challenge, solution],
                               capture_output=True, text=True)
            if b.returncode != 0:
                print(b.stdout + b.stderr)
                print(f"  BUILD FAILED for {config}")
                for thm in theorems:
                    rows.append(("ERROR", thm, config))
                overall = 1
                continue

        for thm in theorems:
            status, detail = check_theorem(challenge, solution, thm)
            print(f"  [{status}] {thm}")
            for line in detail:
                print(line)
            rows.append((status, thm, config))
            if status != "PASS":
                overall = 1

    print()
    print("=" * 70)
    print("Signature pre-flight summary")
    print("=" * 70)
    print(f"{'STATUS':<7}  {'THEOREM':<58}  CONFIG")
    print(f"{'------':<7}  {'-------':<58}  ------")
    for status, thm, config in rows:
        short_cfg = os.path.basename(config)
        print(f"{status:<7}  {thm[:58]:<58}  {short_cfg}")

    print()
    if overall == 0:
        print("All theorems match on universe signature and full type. "
              "Safe to run the full comparator.")
    else:
        print("Mismatches or errors above — the comparator's export check will "
              "reject these. Fix before running landrun.")
    return overall


if __name__ == "__main__":
    sys.exit(main())
