#!/usr/bin/env python3
"""
search_zulip.py — search the Lean (leanprover) Zulip for proof leads / prior art.

Motivation
----------
The survey docs for the formalization effort repeatedly say "READ the exact Zulip thread"
(e.g. the Donsker–Varadhan and Perron–Frobenius discussions): Zulip is where blockers,
half-finished proofs, and "someone already did this" pointers live before they reach a PR.
This is the Zulip analogue of ``search_github_prs.py``.

Auth
----
The Zulip REST API needs credentials. Provide them in the **environment** (never argv):
  ZULIP_EMAIL      your bot/user email on the Zulip realm
  ZULIP_API_KEY    the API key (Settings → Account & privacy → API key, or a bot's key)
  ZULIP_SITE       realm URL; default https://leanprover.zulipchat.com
A standard ``~/.zuliprc`` also works if you point ZULIP_SITE/EMAIL/KEY at its values.
Without creds the tool prints setup instructions and the credential-free fallback (the
public archive) and exits — it does NOT invent results.

Credential-free fallback
-------------------------
The realm is publicly mirrored (read-only, no search API) at
  https://leanprover-community.github.io/archive/   (browsable HTML)
  https://github.com/leanprover-community/archive    (per-stream JSON dumps — clone + grep)
Use those when you have no API key; this tool points you there.

Examples
--------
    export ZULIP_EMAIL=me-bot@leanprover.zulipchat.com ZULIP_API_KEY=...    # set in env
    python3 dev/tools/search_zulip.py "Donsker Varadhan"
    python3 dev/tools/search_zulip.py "Sinkhorn matrix scaling" --num 100
    python3 dev/tools/search_zulip.py "Girsanov" --stream "maths" --num 50

NOTE: this client is written to Zulip's documented ``GET /api/v1/messages`` narrow-search
API but has not been exercised end-to-end in the authoring sandbox (no creds there). If a
field name drifts, check https://zulip.com/api/get-messages and adjust ``fetch``.
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import sys
import urllib.parse
import urllib.request
import urllib.error

ARCHIVE_HTML = "https://leanprover-community.github.io/archive/"
ARCHIVE_REPO = "https://github.com/leanprover-community/archive"


def creds():
    site = os.environ.get("ZULIP_SITE", "https://leanprover.zulipchat.com").rstrip("/")
    email = os.environ.get("ZULIP_EMAIL")
    key = os.environ.get("ZULIP_API_KEY")
    return site, email, key


def fetch(site, email, key, narrow, num_before):
    params = {
        "anchor": "newest",
        "num_before": str(num_before),
        "num_after": "0",
        "narrow": json.dumps(narrow),
        "apply_markdown": "false",
    }
    url = f"{site}/api/v1/messages?" + urllib.parse.urlencode(params)
    auth = base64.b64encode(f"{email}:{key}".encode()).decode()
    req = urllib.request.Request(url, headers={
        "User-Agent": "search_zulip",
        "Authorization": f"Basic {auth}",
    })
    with urllib.request.urlopen(req) as resp:
        return json.load(resp)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("query", help="free-text search operand (Zulip 'search' narrow)")
    p.add_argument("--stream", help="restrict to a stream/channel name")
    p.add_argument("--topic", help="restrict to a topic")
    p.add_argument("--num", type=int, default=60, help="max messages to pull (num_before)")
    p.add_argument("--chars", type=int, default=300, help="content preview length")
    p.add_argument("--format", choices=["text", "json"], default="text")
    args = p.parse_args(argv)

    site, email, key = creds()
    if not (email and key):
        print("[auth] ZULIP_EMAIL / ZULIP_API_KEY not set in environment.\n", file=sys.stderr)
        print("Set them (see script header), then re-run. Credential-free fallback:", file=sys.stderr)
        print(f"  browse : {ARCHIVE_HTML}", file=sys.stderr)
        print(f"  grep   : git clone {ARCHIVE_REPO} && grep -rli '{args.query}' .", file=sys.stderr)
        return 2

    narrow = [{"operator": "search", "operand": args.query}]
    if args.stream:
        narrow.insert(0, {"operator": "stream", "operand": args.stream})
    if args.topic:
        narrow.append({"operator": "topic", "operand": args.topic})

    try:
        data = fetch(site, email, key, narrow, args.num)
    except urllib.error.HTTPError as e:
        print(f"[error] HTTP {e.code}: {e.read()[:300].decode(errors='replace')}", file=sys.stderr)
        return 1

    msgs = data.get("messages", [])
    if args.format == "json":
        print(json.dumps(msgs, indent=2))
        return 0

    print(f"=== {len(msgs)} message(s) matching {args.query!r} ===\n")
    for m in msgs:
        stream = m.get("display_recipient", "?")
        if isinstance(stream, list):  # PM
            stream = "(direct message)"
        topic = m.get("subject", "")
        who = m.get("sender_full_name", "?")
        content = (m.get("content") or "").replace("\n", " ")
        link = f"{site}/#narrow/stream/{m.get('stream_id','')}/near/{m.get('id','')}"
        print(f"[{stream} > {topic}] {who}")
        print(f"  {content[:args.chars]}")
        print(f"  {link}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
