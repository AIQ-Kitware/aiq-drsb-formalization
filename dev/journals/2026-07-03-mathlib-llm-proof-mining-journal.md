# Mining mathlib LLM-tagged PRs for DRSB proof leads — Execution Journal

Date: 2026-07-03
Status: search complete (negative result for the remaining gaps); reusable tooling landed in `dev/tools/`
Scope: `aiq-drsb-formalization` (this repo — `dev/tools/`, `dev/journals/`); part of the broader `aiq-eval-runner` TA1 effort

> Companion to this repo's `SURVEY_LEADS.md` / `FOUNDATIONS.md` (the standing
> external-lead registry + grep-verified Mathlib gap map). This journal records one
> concrete sweep of the **LLM-generated closed-PR pool** and the tools built to repeat it.

## Purpose / trigger

The DRSB Lean formalization has **12 remaining placeholders**, all genuine T4 (see the
submodule's `PROOF_PIPELINE.md` §2):

- **6 SDE/PDE controls** (`ChenGeorgiouPavon2021`): Girsanov energy identity, HJB /
  Hopf–Cole, Léonard gluing, coupling factorization — need stochastic-analysis theory.
- **6 worst-case-structure** (`GaoKleywegt2023` ×3, `MohajerinEsfahaniKuhn2018` ×3): the
  worst-case-measure construction / OT measurable-selection.

Earlier this session the one self-contained target — finite **Sinkhorn / matrix scaling**
existence — was proved from scratch (`ForMathlib.matrix_scaling_exists`, dependency-clean, via
log-domain convex minimization; commit `d6e6ffa` in the submodule). That left the 12 T4
placeholders, which need mathematics absent from the pinned Mathlib.

The question the user raised: **have we exhaustively searched external sources for
LLM-assisted proofs we could bring in — specifically closed, unreviewed, LLM-tagged
mathlib PRs?** (Premise: maintainers close valid proofs merely for being LLM-generated, so
a usable proof may be in the closed-PR graveyard.) The standing registry (`SURVEY_LEADS.md`)
was candid that manual web/GitHub discovery is saturated but the **generated-proof corpora
and the LLM-PR pool were un-mined**. This sweep closes that gap for our specific needs.

## What we checked (and how)

1. **Pinned Mathlib, local grep** (`476fb97b62`): confirmed Kantorovich/OT duality,
   Wasserstein, and Girsanov/Itô are all **absent**; disintegration/`condKernel` **is**
   present (useful for the tractable weak-duality halves). Sion `Mathlib.Topology.Sion`
   present.
2. **Newer Mathlib master** (web): `Analysis/Convex` still has no OT / Kantorovich /
   Fenchel / Legendre. `RemyDegenne/brownian-motion` — Brownian motion complete, Itô "in
   progress", **no Girsanov**. So nothing landed since the pin.
3. **The LLM-PR pool** (GitHub Search API): `repo:leanprover-community/mathlib4 is:pr
   is:closed is:unmerged label:"LLM-generated"` → **414 PRs**. Pulled all 5 pages, filtered
   against the DRSB keyword set (`dev/tools/formalization_terms.txt`).
4. **Whole-repo cross-check**: title/body search across *all* mathlib PRs (any author,
   label, state) for each foundational term.

## Findings

**The theory behind the 12 T4 placeholders is not in the mathlib PR ecosystem — LLM-tagged or
otherwise.** Whole-repo PR search (any author/label/state) returned **zero** hits for:
`Girsanov`, `Kantorovich`, `optimal transport`, `Wasserstein`, `OptimalTransport`,
`Sinkhorn`, `measurable selection`, `Fenchel`/`convex conjugate`, `Feynman Kac`,
`Hamilton Jacobi`. The only active relevant cluster is **Perron–Frobenius** (#39914–#39927,
all *open* human `t-algebra` PRs — Chain 3 infra, which we no longer need since Sinkhorn
scaling was proved directly).

Within the 414 closed-unmerged `LLM-generated` PRs, the only matches to our chains were
**adjacent scaffolds, not our targets**:

| PR | What | Relevance |
|---|---|---|
| #35571 | "Brownian motion, Ito calculus, Black–Scholes PDE" | Chain 4 — but **274 lines / 6 files**, a thin scaffold ("discrete integral for elementary predictable processes"; Black–Scholes PDE in 52 lines). **No Girsanov.** Too shallow to build the SB controls on. |
| #40085, #39349/#39346, #37121, #36641 | Ville / Doob martingale inequalities | Chain-4-adjacent probability infra, not our controls. |
| #36637, #39166, #39167, #38824 | Pinsker / Le Cam / entropy foundational assumptions | Chain-2-adjacent (KL); our DV/Gibbs is already proved. |

On the user's premise (valid proofs closed for being LLM): #35571 was indeed closed
unmerged, but it is genuinely thin — not a complete, unfairly-rejected proof of anything we
need. No substantial, buildable proof of a DRSB-relevant theorem was found in the pool.

**Conclusion:** for the DRSB frontier there is **nothing to vendor** from the LLM-PR pool.
The remaining T4 placeholders require either (a) building the missing Mathlib *area*
(stochastic analysis / general measurable OT) or (b) documented `dependency`s with provenance —
consistent with the standing recommendation. This is a useful *negative* result: it closes
the "did we miss an existing proof?" question for these specific gaps.

## Also checked: external LLM scaffold archives

- **`luaartist/Yang-Mills-Lean-4-Scaffold-Archive`** (153 `.lean`, pushed 2026-06): an
  LLM-generated attempt at the **Yang–Mills mass gap** (a Clay problem). Checked for any
  DRSB-usable analysis. **Verdict: nothing usable, do not depend.** Wrong domain (lattice
  gauge / spectral-gap scaffolding, not OT/DRO/SDE); the closest file
  `GaussianFlowSurgery.lean` is a `structure` whose "guarantees" are bare uninhabited
  `Prop` fields (`stable_chunks_exist : Prop`, `blowup_detection_sound : Prop`, …) — the
  vacuous-scaffold anti-pattern this repo forbids (AGENTS §5). No Girsanov / Itô / optimal
  transport / Kantorovich / Sinkhorn / convex-duality content. **License NOASSERTION**
  (unreusable regardless). Filed here so we don't re-check it.

## What we built (reusable — the user's ask)

`dev/tools/` (in this repo; portable — copy into any formalization):

- **`search_github_prs.py`** — CLI over the GitHub Search API: query any repo by
  label / state / merge-status, filter by regex keyword set, output table/json/csv.
  Auth via `GITHUB_TOKEN` in env (never argv); rate-limit-aware. Reproduces this sweep in
  one command. Tested against the live API (the 414-PR sweep above).
- **`search_zulip.py`** — Zulip narrow-search client (env creds `ZULIP_EMAIL`/`ZULIP_API_KEY`);
  gracefully prints the credential-free public-archive fallback when unset. Written to the
  documented API; not exercised end-to-end here (no creds in sandbox).
- **`formalization_terms.txt`** — curated keyword set grouped by the DRSB/DKPS proof
  chains (OT/convex-duality, Sinkhorn/Perron, KL/Gibbs, SDE/PDE). Copy + tune per project.
- **`README.md`** — usage, auth/rate-limit notes, provenance.

## Recommendations / next moves

1. **LLM-PR pool: exhausted for DRSB.** Re-run `search_github_prs.py` at PR-prep time
   (moving target) but don't expect a rescue for the current 12.
2. **The genuinely un-mined frontier remains the generated-proof *corpora*** (Lean-Workbook,
   OProofs, LeanNavigator, LeanExplore/LeanSearch DBs — see `SURVEY_LEADS.md` §"Generated-
   proof corpora"). Those hold *nearby generated lemmas*, not our exact theorems; lower
   priority than corpus-scale mining would suggest, given the whole-repo zero result.
3. **For the 6 SDE/PDE placeholders:** track `RemyDegenne/brownian-motion` (Itô in progress) and
   `raphaelrrcoelho/formal-mathfin` (partial Girsanov) as future upstream deps; neither is
   mature enough today. Pending them → documented `dependency`s with provenance.
4. **For the 6 worst-case-structure placeholders:** the only realistic in-repo path is the
   **finite/discrete-OT reduction** (empirical nominal ⇒ LP + `Mathlib.Topology.Sion`),
   sidestepping general measurable selection — a real but bounded build, not a vendored
   proof. Decide with the coordinator.
