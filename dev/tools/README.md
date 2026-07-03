# dev/tools — proof-mining utilities

Reusable search tools for formalization work. The recurring need: **"has someone already
proven this lemma in Lean, and is it sitting in a closed / unmerged / unreviewed PR or a
Zulip thread?"** Mathlib maintainers routinely close PRs carrying the `LLM-generated`
label without review, so a valid proof of exactly the lemma you need can live in the
closed-PR graveyard rather than in `master`. These tools sweep that pool in one command.

Stdlib-only Python 3 (no pip installs). Secrets are read from the **environment only**,
never argv (keeps tokens out of `ps`/shell history).

## `search_github_prs.py` — mine GitHub PRs

Query the GitHub Search API for PRs by repo / label / merge-state, filtered against a
keyword set (word-boundary regex by default).

```bash
# The canonical sweep: closed + unmerged LLM-tagged mathlib PRs, filtered to a
# hard-analysis/probability/OT keyword set.
python3 dev/tools/search_github_prs.py --state closed --merged no \
    --label LLM-generated --terms-file dev/tools/formalization_terms.txt --drop-merged-titles

# Does *anyone* (any author/label/state) have a PR mentioning these theorems?
python3 dev/tools/search_github_prs.py --any-state \
    --terms girsanov,kantorovich,wasserstein,sinkhorn --in title,body

# Another repo / label; JSON for scripting.
python3 dev/tools/search_github_prs.py --repo owner/repo --label ai-generated --format json
```

Key flags: `--repo` (default `leanprover-community/mathlib4`), `--label` (repeatable),
`--state {open,closed}` / `--any-state`, `--merged {yes,no,any}` (`no` = the unmerged
graveyard), `--terms` / `--terms-file` / `--default-terms`, `--substring` (literal, not
regex), `--in {title,body,title,body}`, `--extra "created:>2025-01-01"`, `--format
{table,json,csv}`, `--show-body N`.

**Auth / rate limits.** Export `GITHUB_TOKEN` (or `GH_TOKEN`) for 30 search req/min;
without it you get 10/min (fine for a focused sweep). The tool sleeps on the documented
rate-limit headers and backs off on HTTP 403.

`formalization_terms.txt` is the curated keyword set (grouped by the DRSB/DKPS proof
chains: OT/convex-duality, Sinkhorn/Perron, KL/Gibbs, SDE/PDE). Copy + tune per project.

## `search_zulip.py` — search the Lean Zulip

The Zulip analogue (blockers and "someone already did this" pointers land on Zulip before
PRs). Needs credentials in env: `ZULIP_EMAIL`, `ZULIP_API_KEY`, optional `ZULIP_SITE`
(default `https://leanprover.zulipchat.com`). Without creds it prints setup instructions
and the credential-free fallback (the public archive) rather than inventing results.

```bash
export ZULIP_EMAIL=...  ZULIP_API_KEY=...
python3 dev/tools/search_zulip.py "Donsker Varadhan"
python3 dev/tools/search_zulip.py "Girsanov" --stream maths --num 50
```

> The Zulip client is written to the documented `GET /api/v1/messages` narrow-search API
> but has not been exercised end-to-end here (no creds in the authoring sandbox). If a
> field drifts, cross-check <https://zulip.com/api/get-messages>.

## Provenance / what a sweep found (2026-07-03)

First real use of `search_github_prs.py`: swept all **414** closed-unmerged `LLM-generated`
mathlib PRs for the DRSB foundational gaps. Result — **the theory we need is not in the
LLM-proof pool** (no Girsanov, Kantorovich/OT duality, Wasserstein, Sinkhorn/matrix
scaling, measurable selection, Feynman-Kac, or HJB PRs anywhere in mathlib, any
author/state); only adjacent scaffolds (martingale inequalities; a 274-line Brownian/Itô
PR #35571) showed up. Full write-up: `dev/journals/2026-07-03-mathlib-llm-proof-mining-journal.md`.
