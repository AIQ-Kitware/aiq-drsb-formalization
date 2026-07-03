# SURVEY_LEADS.md — external Lean/proof leads to mine & re-check

A dated registry of external artifacts (repos, Mathlib PRs, generated-proof corpora,
Zulip threads, papers) that may supply proofs for the DRSB foundational chains
([`FOUNDATIONS.md`](FOUNDATIONS.md)). Kept so we can **follow up and re-check for updates
later** — many of these are moving targets (open PRs, active repos).

**Last swept: 2026-07-03** (multiple web-survey passes by the coordinator; provenance
uneven; still not exhausted — next layer is generated-proof corpora + declaration search
indices, below).
**Before depending on ANY lead: verify its build status, `sorry` inventory, and license.**
Legend: ⭐ high value · ⚠ low-trust/scaffold · 🔁 moving target (re-check).
Where only a project name is given (no org), find via GitHub **code search** on the
distinctive filename; URLs are recorded when the source gave an exact org/repo.

---

## Use-now / highest value

| Lead | Link | Chain | Note |
|---|---|---|---|
| ⭐ **Mathlib `Topology.Sion`** | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sion.html | 1 | Sion minimax (`minimax'`, `exists_isSaddlePointOn`). **Use directly.** |
| ⭐ **`gpeyre/flow-sinkhorn`** 🔁 | https://github.com/gpeyre/flow-sinkhorn | 3, 1-heavy | Lean Sinkhorn, `KLProjection`, duality, `DualConvergence`, `PrimalDualBounds`, `Applications/OT`, `AppendixEOT`, Pinsker. Grep it for `sorry` first. |
| ⭐ **Mathlib PF PR cluster** 🔁 | #39919 (Collatz–Wielandt / Perron root), #39920 (PF for primitive matrices), #39917 (aux) — https://github.com/leanprover-community/mathlib4/pull/39919 etc. | 3 | Mathlib-native; build PF on these so upstream composes. |
| Mathlib PF merged infra | https://github.com/leanprover-community/mathlib4/pull/28728 | 3 | Irreducible+Primitive matrices + Quiver links (merged Jul 2025). |
| Mathlib `cgf`/`mgf` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Basic.html | 2 | log-partition = `ProbabilityTheory.cgf`. Use. |
| ⭐ **`StatLean` / `Stat-Lean`** | GitHub code search: `KLDivergence.lean`, `PinskerInequality.lean`, `GaussianKLMulti.lean` | 2 | native KL / Pinsker / Gaussian-KL / Fano / mutual-info; "for-Mathlib" quality — could ease the outer DV/Lagrangian layer |
| ⭐ **Mathlib doubly-stochastic API** | `Analysis/Convex/Birkhoff.lean`, `Analysis/Convex/DoublyStochasticMatrix.lean`, `LinearAlgebra/Matrix/Stochastic.lean` | 3 | native finite-dim stochastic/doubly-stochastic matrix API — **start the Sinkhorn build here**, not from PF (see FOUNDATIONS.md Chain 3) |

## Chain 2 — Donsker–Varadhan / KL / Gibbs / PAC-Bayes

> We already have the **full DV equality proved** in `ForMathlib` — these are for KL
> lemmas / Boué–Dupuis / alternate proofs, not the DV equality itself.

| Lead | Link | AI? | Note |
|---|---|---|---|
| DV Zulip thread ⭐ | `leanprover-community/archive` → `On Potentially Formalizing Donsker Varadhan.json` (https://github.com/leanprover-community/archive) | — | first stop for Chain-2 context, blockers, who's working nearby |
| `mrdouglasny/gibbs-variational` | https://github.com/mrdouglasny/gibbs-variational | unclear | DV **inequality** proved; equality is `sorry` & false-as-written (`.toReal`). Ours supersedes. Mine KL lemmas / Boué–Dupuis bound. |
| `Robby955/FormalSLT` | https://github.com/Robby955/FormalSLT | mixed | PAC-Bayes KL / McAllester / change-of-measure; also `statlean-v0.1.jsonl` (structured theorem map — mine it) |
| `hawkrobe/linglib` | https://github.com/hawkrobe/linglib | mixed | `GibbsVariational.lean`, RSA Gibbs material |
| `the-omega-institute/automath` | https://github.com/the-omega-institute/automath | mixed | `XiReverseKLDVPoissonVariational.lean` (reverse-KL DV) |
| `FujiHaruka/information-theory` | https://github.com/FujiHaruka/information-theory | mixed | KL variational lower / Fatou / inventory docs |
| `szl-holdings/lutar-lean` | https://github.com/szl-holdings/lutar-lean | mixed | `TimeUniformPACBayes.lean` |
| `bangyen/leansharp` | https://github.com/bangyen/leansharp | mixed | `PacBayesBasis.lean` |
| `mlinegar/ThinkingTrees` ⚠ | https://github.com/mlinegar/ThinkingTrees | — | Lean 3, variational-bound-adjacent; likely stale |

## Chain 1 roots — convex analysis / Fenchel (author ourselves; no direct hit)

| Lead | Link | Note |
|---|---|---|
| AMBER (Construction-Verification) | https://arxiv.org/abs/2602.01291 | applied-math bench: convex analysis, optimization, numerical algebra, high-dim prob — closest terrain for Fenchel scaffolding |
| CAM-Bench | https://arxiv.org/abs/2605.17255 · repo `optpku/CAM-Bench` https://github.com/optpku/CAM-Bench | 1000 applied-math Lean targets (optimization, numerical LA) |
| `iamkarthikbk/edith` ⚠ | https://github.com/iamkarthikbk/edith | `GeometricProgramming.lean`; low-trust, convex/duality-adjacent |
| Mathlib `label:LLM-generated Analysis Convex Gauge` | (PR search, see recipes below) | Convex/Gauge API terrain — not Fenchel, but adjacent |

## Chain 1-heavy — Kantorovich / Wasserstein / general OT (scaffolds only; defer)

| Lead | Link | Note |
|---|---|---|
| `gpeyre/flow-sinkhorn` (again) | https://github.com/gpeyre/flow-sinkhorn | `Applications/OT`, `AppendixEOT` — entropic-OT duality, the realistic OT angle |
| `lean-eval-leaderboard` ⚠ | GitHub code search: `ProblemMongeKantorovich.lean` | benchmark scaffold, not a mature branch |
| `LeanAide` ⚠ | GitHub code search: `Kantorovich_old_aristotle.lean` (Aristotle-generated) | scaffold |
| `athanor-ai/pythia` ⚠ | https://github.com/athanor-ai/pythia | `OptimalTransport/WassersteinDistanceNonneg.lean` |

> Strategy: **reduce to finite/discrete OT** (LP + Sion) to sidestep general measurable OT.

## Chain 3 — Perron–Frobenius / matrix positivity (beyond the cluster above)

| Lead | Link | Note |
|---|---|---|
| `mrdouglasny/spectral-positivity` | https://github.com/mrdouglasny/spectral-positivity · file: https://raw.githubusercontent.com/mrdouglasny/spectral-positivity/main/SpectralPositivity/Matrix/PerronFrobenius.lean | PF, Jentzsch, Collatz–Wielandt eigenvector |
| `mrdouglasny/pphi2` | https://github.com/mrdouglasny/pphi2 | `TransferMatrix/Positivity.lean` — positivity-transfer lemmas |
| `LionSR/TNLean` | https://github.com/LionSR/TNLean | `TNLean/QPF/Primitive.lean` — "primitive"/transfer-matrix adjacent |
| `selfreferencing/Agentic-Capital-Desktop` ⚠ | https://github.com/selfreferencing/Agentic-Capital-Desktop | `PROMPT_3_PERRON_FROBENIUS_COMPLETE.md`; scaffolded, low trust |
| `mkaratarakis/HopfieldNet` | https://github.com/mkaratarakis/HopfieldNet · paper https://arxiv.org/abs/2512.07766 | Hopfield/Boltzmann formalization proving ergodicity via a **new PF formalization** — a PF trail independent of the Mathlib PR cluster |

## Chain 4 — stochastic analysis (defer; radar only)

| Lead | Link | Note |
|---|---|---|
| `RemyDegenne/brownian-motion` 🔁 | https://github.com/RemyDegenne/brownian-motion | Brownian motion complete; Itô/stochastic integral in progress |
| `raphaelrrcoelho/formal-mathfin` 🔁 | https://github.com/raphaelrrcoelho/formal-mathfin | Itô core; `MathFin/Foundations/FeynmanKacHeatEquation.lean`, `MathFin/Blueprint.lean`; partial Girsanov; disclosed gaps |
| Brownian motion in Lean (paper) | https://arxiv.org/abs/2511.20118 | construction of Brownian motion |
| Verified math-finance library (paper) | https://arxiv.org/abs/2606.01356 | L2 Itô integral, risk-neutral pricing measure |

## Declaration search engines (find hidden supporting lemmas — semantic, not name-match)

| Tool | Link | Use |
|---|---|---|
| LeanExplore | https://arxiv.org/abs/2506.11085 | indexes declarations across many Lean packages; downloadable DB/API |
| LeanSearch v2 | https://arxiv.org/abs/2605.13137 | global-premise retrieval + benchmark |
| Moogle / LeanSearch / `loogle` | (web) | quick premise/lemma lookup by type/name |

Use these for the *supporting* lemmas (convexity, stochastic matrices, KL, finite sums,
eigenvalues) rather than the top-level theorems.

## Generated-proof corpora — QUERY THESE (ordinary GitHub search misses them)

The search-strategy shift: mine large generated/searched-proof datasets for the query
terms below, rather than more theorem-name GitHub searches.

| Corpus | Link | What |
|---|---|---|
| Lean-GitHub | https://arxiv.org/abs/2407.17227 | compiled ~all Lean4 GitHub repos (InternLM) |
| Lean-Workbook / InternLM2.5-StepProver | https://arxiv.org/abs/2410.15700 | searched proofs over large Lean problem sets |
| OProofs / OProver | https://arxiv.org/abs/2605.17283 | 1.77M statements, 6.86M verified proofs, agentic trajectories (incl. failures/repairs) |
| LeanNavigator | https://arxiv.org/abs/2503.04772 | 4.7M generated theorems/proofs via state-transition graphs over Mathlib4 |
| AXLE / Axiom Math | https://arxiv.org/abs/2606.26442 · https://prover.axiomatic-ai.com/ · Putnam2025 https://reservoir.lean-lang.org/@AxiomMath/Putnam2025 | proof extraction/verify/repair infra + generated artifacts |
| Goedel-Prover / V2 | https://arxiv.org/abs/2502.07640 · https://arxiv.org/abs/2508.03613 | 29.7K generated Lean-Workbook proofs; released models/code/data |
| Leanabell-Prover-V2 | https://arxiv.org/abs/2507.08649 | verifier-integrated repair trajectories; released data/models |
| DeepSeek-Prover-V2 | https://arxiv.org/abs/2504.21801 | recursive subgoal decomposition; ProverBench |
| LeanMarathon | https://arxiv.org/abs/2606.05400 | long-horizon Lean projects (blueprint/DAG); agent-produced structure |
| Lean Refactor | https://arxiv.org/abs/2605.20244 | refactor patterns / proof-strategy DB for cleaning generated attempts |

> These agent-prover mines rarely hold our exact theorems but often hold **nearby
> generated lemmas** (convexity, KL, finite sums, matrices) worth repurposing.

**Priority query terms** (for corpora AND `label:LLM-generated` PR search):
```
Donsker Varadhan · Gibbs variational · KL variational · PAC Bayes
Fenchel · Legendre · convex conjugate
Kantorovich · Wasserstein · optimal transport · coupling · cTransform · Lipschitz
Sinkhorn · KLProjection · matrix scaling
Perron Frobenius · Collatz Wielandt · primitive matrix
Feynman Kac · Girsanov · Ito
```

## Mathlib PR search recipes (what actually worked)

- **`label:LLM-generated` × AREA, not theorem name.** Exact theorem-term searches were
  mostly empty; area clusters productive: `label:LLM-generated LinearAlgebra Matrix`
  (→ `Matrix/Nondegenerate`, …), `label:LLM-generated Analysis Convex Gauge`,
  `label:LLM-generated Analysis` (→ RKHS/spectral).
- **Prover-name searches** beyond the label: `Seed Prover`, `lean-eval`, `Aristotle`,
  `Harmonic` (e.g. a symplectic-determinant PR credited to Seed Prover / lean-eval).
- **"Agent golf" index PRs** map LLM-touched areas (not theorem sources): #37968,
  #38104 (MeasureTheory), #38144 (NumberTheory); query "Extracted from #37968".
- **Zulip `AI-authored-projects`** channel — closed/generated-PR discovery surface
  (also the `AI-assisted MDS and spectral PRs` topic).

## Re-check cadence
The 🔁 items (flow-sinkhorn, the PF PR cluster, brownian-motion, formal-mathfin) are
active — re-sweep before starting the corresponding chain, and again at PR-prep time
(Mathlib master moves; a gap may have closed). Update **Last swept** above when you do.
