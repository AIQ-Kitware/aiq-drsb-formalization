#!/usr/bin/env python3
"""
search_github_prs.py — mine GitHub pull requests for (LLM-assisted) proofs.

Motivation
----------
Formalization work repeatedly needs to answer: "has anyone already proven this in
Lean, and is it sitting in a *closed / unmerged / unreviewed* PR?" Mathlib maintainers
routinely close PRs carrying the ``LLM-generated`` label without review, so a valid proof
of exactly the lemma you need may be one search away — in the closed-PR graveyard rather
than in ``master``. This tool queries the GitHub Search API for PRs by repo / label /
merge-state and filters them against a keyword set (word-boundary regex by default), so a
future formalization can sweep the LLM-proof pool in one command instead of ad-hoc curl.

It is deliberately general (any repo, any label, any terms) — the mathlib + ``LLM-generated``
defaults are just the common case.

Auth & rate limits
-------------------
Reads a token from ``GITHUB_TOKEN`` (or ``GH_TOKEN``) in the **environment only** — never
from argv (keeps the secret out of ``ps`` / shell history; mirrors the repo's
secret-hygiene rule). Unauthenticated: 10 search req/min. Authenticated: 30/min. The tool
sleeps adaptively on the documented rate-limit headers and backs off on HTTP 403.

Examples
--------
# The exact sweep that motivated this tool: closed + unmerged LLM PRs, filtered to a
# formalization keyword set (Girsanov, Kantorovich, Sinkhorn, ...):
    python3 dev/tools/search_github_prs.py --state closed --merged no \
        --label LLM-generated --terms-file dev/tools/formalization_terms.txt

# Does *anyone* (any author/label/state) have a PR mentioning these theorems?
    python3 dev/tools/search_github_prs.py --any-state \
        --terms girsanov,kantorovich,wasserstein,sinkhorn --in title,body

# A different repo / label, JSON out for scripting:
    python3 dev/tools/search_github_prs.py --repo owner/repo --label ai-generated \
        --format json > hits.json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request
import urllib.error

API = "https://api.github.com/search/issues"

# A broad default keyword set for hard-analysis / probability / optimal-transport
# formalization mining. Override with --terms or --terms-file for other domains.
DEFAULT_TERMS = [
    # optimal transport / convex duality
    r"optimal transport", r"kantorovich", r"wasserstein", r"\bmonge\b", r"c-transform",
    r"fenchel", r"convex conjugate", r"legendre transform", r"rockafellar",
    r"measurable selection", r"\bminimax\b", r"\bsion\b",
    # entropic / Sinkhorn / matrix scaling / Perron
    r"\bsinkhorn\b", r"matrix scaling", r"doubly[- ]stochastic", r"birkhoff",
    r"perron", r"frobenius(?! number)", r"collatz[- ]wielandt", r"entropic",
    # information theory / KL
    r"donsker", r"varadhan", r"\bpinsker\b", r"relative entropy", r"\bkl div",
    # stochastic analysis / SDE / PDE control
    r"girsanov", r"\bit[oô]\b", r"stochastic integral", r"stochastic differential",
    r"\bsde\b", r"semimartingale", r"\bmartingale", r"brownian", r"feynman",
    r"hamilton[- ]jacobi", r"\bbellman\b", r"schr[oö]dinger", r"fokker",
]


def build_query(args) -> str:
    q = [f"repo:{args.repo}", "is:pr"]
    if not args.any_state:
        q.append(f"is:{args.state}")
    if args.merged == "yes":
        q.append("is:merged")
    elif args.merged == "no":
        q.append("is:unmerged")
    for lab in args.label or []:
        q.append(f'label:"{lab}"')
    if args.extra:
        q.append(args.extra)
    return " ".join(q)


def gh_get(url: str, token: str | None):
    headers = {"User-Agent": "search_github_prs", "Accept": "application/vnd.github+json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, headers=headers)
    for attempt in range(6):
        try:
            resp = urllib.request.urlopen(req)
            data = json.load(resp)
            remaining = resp.headers.get("X-RateLimit-Remaining")
            if remaining is not None and int(remaining) <= 1:
                reset = int(resp.headers.get("X-RateLimit-Reset", "0"))
                wait = max(2, reset - int(time.time()) + 1) if reset else 6
                print(f"[rate-limit] sleeping {wait}s", file=sys.stderr)
                time.sleep(min(wait, 65))
            return data
        except urllib.error.HTTPError as e:
            if e.code in (403, 429):
                retry = int(e.headers.get("Retry-After", "0")) or (2 ** attempt) * 5
                print(f"[rate-limit] HTTP {e.code}; backing off {retry}s", file=sys.stderr)
                time.sleep(min(retry, 65))
                continue
            raise
    raise RuntimeError("gave up after repeated rate-limit backoffs")


def fetch_all(query: str, token: str | None, hard_cap: int):
    items, page = [], 1
    while len(items) < hard_cap:
        url = f"{API}?q={urllib.parse.quote(query)}&per_page=100&page={page}"
        data = gh_get(url, token)
        total = data.get("total_count", 0)
        batch = data.get("items", [])
        items.extend(batch)
        if page == 1:
            print(f"[query] {query}\n[total_count] {total}", file=sys.stderr)
        if not batch or len(items) >= min(total, 1000):  # search API caps at 1000
            break
        page += 1
    return items[:hard_cap]


def compile_terms(terms, substring: bool):
    pats = []
    for t in terms:
        pats.append(re.escape(t) if substring else t)
    return re.compile("|".join(pats), re.I) if pats else None


def haystack(item, where: str) -> str:
    body = item.get("body") or ""
    if where == "title":
        return item["title"]
    if where == "body":
        return body
    return item["title"] + "\n" + body


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--repo", default="leanprover-community/mathlib4")
    p.add_argument("--label", action="append", help="repeatable; e.g. --label LLM-generated")
    p.add_argument("--state", choices=["open", "closed"], default="closed")
    p.add_argument("--any-state", action="store_true", help="ignore --state (open+closed)")
    p.add_argument("--merged", choices=["yes", "no", "any"], default="any",
                   help="'no' = closed-but-unmerged (the LLM graveyard)")
    p.add_argument("--terms", help="comma-separated keyword filters (regex unless --substring)")
    p.add_argument("--terms-file", help="one keyword/regex per line (# comments allowed)")
    p.add_argument("--default-terms", action="store_true",
                   help="use the built-in hard-analysis/probability/OT term set")
    p.add_argument("--substring", action="store_true", help="literal substring match, not regex")
    p.add_argument("--in", dest="where", choices=["title", "body", "title,body"], default="title,body")
    p.add_argument("--extra", help="raw extra GitHub search qualifiers, e.g. 'created:>2025-01-01'")
    p.add_argument("--drop-merged-titles", action="store_true",
                   help="drop items whose title contains '[Merged by Bors]' (belt-and-braces)")
    p.add_argument("--limit", type=int, default=1000)
    p.add_argument("--format", choices=["table", "json", "csv"], default="table")
    p.add_argument("--show-body", type=int, default=0, help="print N chars of body per hit (table)")
    args = p.parse_args(argv)

    terms = []
    if args.terms:
        terms += [t.strip() for t in args.terms.split(",") if t.strip()]
    if args.terms_file:
        with open(args.terms_file) as f:
            terms += [ln.strip() for ln in f if ln.strip() and not ln.lstrip().startswith("#")]
    if args.default_terms or (not terms and not args.terms and not args.terms_file):
        # if no filter requested at all, still allow (label-only sweeps); only auto-load
        # defaults when explicitly asked, to avoid surprising empty results.
        if args.default_terms:
            terms += DEFAULT_TERMS
    rx = compile_terms(terms, args.substring)

    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        print("[auth] no GITHUB_TOKEN/GH_TOKEN in env — unauthenticated (10 req/min)", file=sys.stderr)

    items = fetch_all(build_query(args), token, args.limit)

    rows = []
    for it in items:
        if args.drop_merged_titles and "[Merged by Bors]" in it["title"]:
            continue
        matched = None
        if rx is not None:
            m = sorted({x.lower() for x in rx.findall(haystack(it, args.where))})
            if not m:
                continue
            matched = m
        merged = bool(it.get("pull_request", {}).get("merged_at"))
        rows.append({
            "number": it["number"],
            "title": it["title"],
            "url": it["html_url"],
            "state": "merged" if merged else it["state"],
            "labels": [l["name"] for l in it.get("labels", [])],
            "matched": matched or [],
            "body": (it.get("body") or ""),
        })

    if args.format == "json":
        for r in rows:
            r.pop("body", None) if not args.show_body else r.__setitem__("body", r["body"][:args.show_body])
        print(json.dumps(rows, indent=2))
    elif args.format == "csv":
        import csv
        w = csv.writer(sys.stdout)
        w.writerow(["number", "state", "title", "url", "matched"])
        for r in rows:
            w.writerow([r["number"], r["state"], r["title"], r["url"], "|".join(r["matched"])])
    else:
        print(f"\n=== {len(rows)} hit(s) ===\n")
        for r in sorted(rows, key=lambda x: -x["number"]):
            print(f"#{r['number']} [{r['state']}] {r['title']}")
            if r["matched"]:
                print(f"     match={r['matched']}")
            print(f"     {r['url']}")
            if args.show_body and r["body"]:
                print("     | " + r["body"][:args.show_body].replace("\n", " ") + " ...")
    print(f"\n[done] {len(rows)} hit(s) of {len(items)} fetched", file=sys.stderr)


if __name__ == "__main__":
    main()
