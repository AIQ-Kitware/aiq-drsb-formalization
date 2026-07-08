# PAPER.md — draft narrative & outline for the AI-formalization method paper

Living outline for a paper on **our method for AI-assisted formalization of research
claims**, grown alongside the work (DKPS + DRSB). Not prose yet — a scaffold of thesis,
contributions, section plan, and the two original ideas (the *survey-and-stage* method
and **`mathlib-slop`**). Companions: [`FOUNDATIONS.md`](FOUNDATIONS.md) (the chains),
[`SURVEY_LEADS.md`](SURVEY_LEADS.md) (the raw related-work survey),
[`PROOF_PIPELINE.md`](PROOF_PIPELINE.md) (the tiered work plan).

Scope note: the *method* spans both sibling repos — `aiq-dkps-formalization` (JHU DKPS;
the Gram→Courant–Fischer→Weyl→Davis–Kahan→MDS chain, already `ForMathlib`-staged) and
`aiq-drsb-formalization` (this repo). The paper draws case studies from both.

---

## 1. Thesis & contributions

**Thesis.** Formalizing a *research* claim (not an olympiad problem) is rarely one
theorem — it is a **chain of classical results**, many absent from Mathlib. Progress is
gated less by raw proving ability than by (a) knowing which links already exist across a
fragmented AI/human proof ecosystem, and (b) having a *home* for the true-but-not-
Mathlib-shaped lemmas the chain needs. We contribute a method for (a) and a proposal for
(b).

**Contributions.**
1. **Survey-and-stage**, a reproducible method: decompose the target into a dependency
   DAG of named classical theorems; *survey* existing AI/human Lean proofs before
   proving; *stage* the reusable, general links in a `ForMathlib` layer and author only
   the genuine gaps; *adversarially verify*; *account* for compute cost per commit.
2. **A survey of the AI-generated-Lean-proof ecosystem** (provers, corpora, search
   indices, domain libraries, benchmarks) and an empirical **coverage finding**: the
   ecosystem is *vast in volume but thin in coverage* of any one research target's chain
   (millions of generated proofs; near-zero hits on our load-bearing links).
3. **SLOP** (*Sound Library of Open Proofs*; nickname "slop"): a permissive,
   machine-verified, *searchable* companion library that accepts AI proofs of any calibre
   so long as they are true — the missing home for staged research lemmas — with per-proof
   provenance, attribution, and measured compute cost.
4. **Two case studies** (DKPS spectral chain; DRSB DRO/Schrödinger-bridge chains) with a
   concrete "what already existed vs. what we had to build" ledger.
5. **Measured resource accounting** of the formalization itself (tokens/model/energy per
   commit) — to our knowledge a first for a formalization library.

---

## 2. Motivation — the gap Mathlib leaves for research formalization

- Research claims rest on long chains; Mathlib covers the trunk (measure theory, linear
  algebra) but not the applied leaves (OT/Kantorovich duality, Sinkhorn scaling, SDE/
  Girsanov, DRO duality — all grep-verified absent for DRSB).
- Mathlib's bar is (rightly) **maintainability + generality + notability**, plus a
  cautious AI-contribution policy and slow human review. Consequence: a *true, useful,
  machine-checked* lemma produced for a specific formalization often has **no home** — it
  is too specific, too AI-shaped, or simply stuck in review.
- **Anecdote (motivating, first-person):** a Gram-rigidity proof from the DKPS effort was
  rejected from Mathlib despite being correct and useful — friction that discards verified
  work and discourages the exact contributions research formalization generates.
- The reaction is not "lower Mathlib's bar" but "**build a second tier**" with a different
  contract — verified truth over curated maintainability — and make it *searchable* so the
  work is reusable even if it never lands upstream.

---

## 3. Method — survey-and-stage

1. **Edge statement.** State the idealized theorem the card/claim rests on, plus the
   explicit "assumption → relaxation" edges to the empirical code (the AIQ TA1
   *formalization-edge* framing). Fixes *what the proof guarantees vs. what is measured*.
2. **Chain decomposition.** Expand each target into a DAG of named classical results;
   grep-verify each link's Mathlib status (**never trust memory; never `head`-truncate a
   gap check** — that hid Sion's minimax from us). See `FOUNDATIONS.md`.
3. **Survey before proving**, in two phases. (a) *Manual discovery* — web/GitHub/Zulip/
   registry search per link; this saturates quickly (we hit diminishing returns after a
   few passes). (b) *Bulk corpus mining* — scripted exact+fuzzy search over the large
   generated-proof datasets (Lean-GitHub, Lean-Workbook, LeanNavigator, OProofs) and
   declaration indices (LeanExplore, LeanSearch v2), which is where the remaining hits (if
   any) live. Record every lead with URL + provenance + status in a dated registry
   (`SURVEY_LEADS.md`) so moving targets can be re-checked. **"Exhausted" means the corpus
   pass, not just manual search, came up empty.**
4. **Stage & author.** Put reusable general links in `ForMathlib/<Mathlib dest path>`
   (Mathlib-aspiring) and/or `mathlib-slop` (permissive). Author only the true gaps. Rewire
   paper libraries to *consume* staged lemmas (e.g. DRSB `exists_worstCase_gibbs` consumes
   `ForMathlib…Normalization`; `sinkhorn_potentials_exist` delegates to a staged stub).
5. **Adversarially verify.** Lean dependency audit on each leaf; independent skeptic passes;
   multiple proofs per theorem welcomed (robustness + a golf race). Flag under-specified
   statements (we found two: `primal_feasible_iff`, and a missing mass-conservation
   hypothesis in the Sinkhorn scaling statement).
6. **Account.** Measure tokens/model/(energy) per commit (`dev/resource_tally`), attaching
   a compute cost to each proof — feeding both reproducibility and the climate-cost story.

---

## 4. Related work = the survey (taxonomy + coverage finding)

Structure the related-work section as a **taxonomy of AI-proof sources** (all catalogued
with links in `SURVEY_LEADS.md`):
- **Provers / agents:** Goedel-Prover(-V2), Leanabell-Prover-V2, DeepSeek-Prover-V2,
  Seed Prover, external proof-search tooling, InternLM StepProver.
- **Generated corpora:** Lean-GitHub, Lean-Workbook, LeanNavigator (4.7M), OProofs (6.86M).
- **Declaration search indices:** LeanExplore, LeanSearch v2, Moogle, loogle.
- **Domain libraries:** StatLean (KL/Pinsker/Fano), flow-sinkhorn (Sinkhorn/OT),
  spectral-positivity (Perron–Frobenius), gibbs-variational (DV), formal-mathfin /
  brownian-motion (stochastic analysis).
- **Benchmarks:** CAM-Bench, AMBER, ProverBench, LeanMarathon.

**Coverage finding (the empirical hook).** Despite this volume, for the DRSB chains we
found: Sion ✅ (Mathlib), cgf & doubly-stochastic ✅ (Mathlib), a few *adjacent* external
repos of unverified status — and **essentially zero ready-to-use proofs of the
load-bearing links** (OT/DRO weak/strong duality, Sinkhorn scaling, the DV *equality*).
The one close external DV hit (`gibbs-variational`) proves only the inequality and its
equality is placeholder and false-as-written (`.toReal` on infinite KL) — a trap we
independently avoided. **We had to build the load-bearing results ourselves.** Quantify
this as a coverage metric per chain (found-and-usable / found-but-unusable / absent).

---

## 5. SLOP — Sound Library of Open Proofs (a permissive, searchable home for verified AI proofs)

*Name: **SLOP** = **S**ound **L**ibrary of **O**pen **P**roofs — the acronym is the
affectionate nickname ("slop"), the expansion states the contract: **sound** = every entry
is machine-checked true. Alternatives if we drop the backronym: "the Annex",
"Mathlib-Bazaar" (cathedral-vs-bazaar), "Compost" (slop that becomes fertile). Repo handle
could be `mathlib-slop`.*

**One line:** a Mathlib companion that accepts AI proofs of *any calibre as long as they
are true (machine-checked)*, indexes them for search, and curates lightly — the opposite
end of the trade-off from Mathlib.

**Acceptance contract (CI-enforced, low bar):**
- compiles against a pinned Mathlib; **no placeholder**; Lean dependency audit clean (or declared
  dependencies listed);
- carries a machine-readable **statement + provenance** (model, session, tokens, date,
  and — our twist — measured compute/energy cost);
- **attribution + license** for any adapted/vendored proof: original author, source repo
  + commit permalink, compatible license (per `SURVEY_LEADS.md`'s vendoring policy) —
  verified truth never waives credit;
- **not required:** Mathlib style, maximal generality, notability, or long-term
  maintainability.

**Design principles:**
- **Multiple proofs per theorem are a feature** (robustness, a golf/quality race,
  training data), not a duplication smell — mirrors the DKPS `Challenge/…/Leaderboard`
  pattern already in use.
- **Searchable by construction:** every declaration indexed (LeanExplore/LeanSearch-style
  embeddings + type/name) so the library is a *reuse* surface, not a graveyard.
- **Light, post-hoc curation:** on a Mathlib bump, prune what breaks and is unmaintained;
  tag usefulness/centrality; keep everything true. "Slop" is a feature name, not an
  insult — volume + verification + search beats gatekeeping for *discovery*.
- **A promotion pipeline to Mathlib:** slop → (golf + generalize) → `ForMathlib` staging →
  Mathlib PR. Rejection from Mathlib demotes to slop, it does not delete the work.
- **Provenance & cost ledger** per theorem (ties to `dev/resource_tally`): the first
  library to track *what it cost to prove each lemma*.

Open questions for the paper: trust model (who can push; is CI-green enough?); dedup vs.
diversity; naming/namespacing at scale; license; how search ranking handles many proofs
of one statement; governance vs. Mathlib.

---

## 6. Case studies — what existed vs. what we built

| Link | Chain | Pre-existing? | Outcome |
|---|---|---|---|
| Sion minimax | DRSB-1 | ✅ Mathlib `Topology.Sion` | reuse |
| cgf / log-partition | DRSB-2 | ✅ Mathlib `cgf` | reuse |
| doubly-stochastic / Birkhoff | DRSB-3 | ✅ Mathlib | reuse (revised Sinkhorn plan onto it) |
| Donsker–Varadhan *variational equality* | DRSB-2 | ⚠ only inequality externally (`gibbs-variational`, buggy equality) | **built, dependency-clean** (`ForMathlib…DonskerVaradhan`) |
| OT-DRO per-coupling weak-duality bound | DRSB-1 | ❌ (no OT duality in Mathlib) | **built** (`ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost`, ported+generalized) |
| finite-measure normalization | DRSB-2 | ❌ (only `tilted_const'` indirectly) | **built** (`ForMathlib…Normalization`), consumed by a paper lemma |
| Gibbs worst-case normalization; static-SB=entropic-OT; Lc-dual eq. | DRSB | ❌ | **built** (paper-lib leaves) |
| Sinkhorn / matrix scaling | DRSB-3 | ❌ core (external `flow-sinkhorn`, unverified) | staged; author on doubly-stochastic API |
| DRO strong-duality `≥` / measurable selection; SDE/Girsanov | DRSB-1/4 | ❌ (missing Mathlib *area*) | deferred / documented |
| Gram rigidity, Courant–Fischer, Weyl, Davis–Kahan, MDS | DKPS | mixed (some Mathlib, some ours) | staged in DKPS `ForMathlib`; **Gram rigidity rejected upstream → the slop motivation** |

Takeaway: reuse where Mathlib reaches; **the research-specific chain links are where the
proving actually happened**, and they are exactly the ones with no upstream home.

---

## 7. Evaluation & measurement
- **Coverage metric** per chain (found-usable / found-unusable / absent) — the survey
  finding, quantified.
- **Compute-cost ledger** per proved lemma (tokens, model, energy) from `resource_tally`.
- **Verification integrity:** Lean dependency audit leaf audits; count under-specified statements
  caught (2 so far); multiple-proof agreement where available.

## 8. Threats / limitations
- Survey recall is a moving target (corpora + Mathlib master change) — mitigated by the
  dated, re-checkable registry.
- "True but unmaintainable" slop risks bit-rot on Mathlib bumps — the curation policy is
  the answer, but its cost is unquantified.
- Abstracted analytic objects (no Mathlib SDE theory) mean some DRSB statements are
  faithful-but-unproven (T4) — honest scoping, not hidden.

## 9. Next steps (to turn this into a paper)
1. Finalize the coverage table (per-link found/built) and compute-cost numbers.
2. Land the card critical path (weak-duality assembly → cost bounds) as the "it actually
   proves the claim" result.
3. Stand up a minimal **SLOP** prototype repo (CI acceptance contract + a search index)
   seeded with our staged lemmas + the DKPS rejects (e.g. the rejected Gram-rigidity proof).
4. Write §4 (survey) from `SURVEY_LEADS.md`; write §5 (slop) from §5 here.
5. Decide venue framing: formalization methods / AI4Math / DRO-formalization case study.
