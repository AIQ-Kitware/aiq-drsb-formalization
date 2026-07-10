# AIQ DRSB Formalization

Lean 4 formalization of the mathematical claims underlying the GaTech **DRSB**
(Distributionally-Robust Schrödinger Bridge) TA1 evaluation cards. The repository has
one library per theorem-bearing source paper, a paper-agnostic `ForMathlib` staging
library, a `Drsb` capstone, and source-oriented prose under [`prose/`](prose/).

> **Start with [`AGENTS.md`](AGENTS.md).** It records the project purpose, provenance
> rules, workflow, and known traps. For a dated account of the checked source state,
> read [`STATUS.md`](STATUS.md). Do not infer current status from old journal or planning
> entries.

## The evaluation-card claims

The two card-facing declarations are in [`Drsb/Basic.lean`](Drsb/Basic.lean):

- `Drsb.wdrsb_cost_bound` corresponds to `wdrsb_cost_bound.yaml`;
- `Drsb.sdrsb_cost_bound` corresponds to `sdrsb_cost_bound.yaml`.

Both prove a one-sided expectation bound of the form

```text
E_mu[V] <= a Wasserstein- or Sinkhorn-DRO dual worst-case bound,
```

for a source distribution `mu` in the relevant ambiguity ball. The value function
`V : X -> R` is abstract in these two declarations. Its intended Schrödinger-bridge /
stochastic-control interpretation comes from Chen--Georgiou--Pavon, but the continuum
construction of that `V` is not a proof-term dependency of either card theorem.

The card claims are specializations of published DRO results rather than verbatim
statements from a single DRSB paper:

| Card theorem | Published backing | Relationship |
|---|---|---|
| `Drsb.wdrsb_cost_bound` | Blanchet--Murthy; Gao--Kleywegt | quadratic-cost Wasserstein-DRO specialization and weak-duality consequence |
| `Drsb.sdrsb_cost_bound` | Wang--Gao--Xie | Sinkhorn-DRO log-partition specialization and weak-duality consequence |
| interpretation of `V` | Chen--Georgiou--Pavon | mathematical provenance; abstract at the card-theorem boundary |

The source-faithful strong-duality and worst-case-structure developments are valuable
parallel formalizations. They are not dependencies of the two card inequalities unless a
specific declaration says otherwise.

## Libraries

| Library | Role | Representative declarations |
|---|---|---|
| `ForMathlib` | Paper-agnostic staging for KL/Donsker--Varadhan, OT/DRO, measurable selection, finite matrix scaling, projective metrics, and continuum support | `log_integral_exp_eq_sSup`, `OT.dualValue_le_droValue`, `matrix_scaling_exists`, `positive_kernel_birkhoff_hopf_contraction` |
| `ChenGeorgiouPavon2021` | SB/SOC/entropic-OT, finite Sinkhorn convergence, and sequence/path-space targets | `schrodingerBridge_KL_eq_SOC`, `sinkhorn_potentials_exist`, `energy_identity_sequenceModel` |
| `BlanchetMurthy2019` | Wasserstein-DRO source-facing theorems | `wdro_strong_duality` |
| `GaoKleywegt2023` | Wasserstein-DRO duality and worst-case structure | `strong_duality_thm1_of_regularity`, `worstCase_structure_cor1` |
| `MohajerinEsfahaniKuhn2018` | Data-driven Wasserstein-DRO reformulation and structured worst-case laws | `worstCaseExpectation_eq_dual`, `worstCase_exists` |
| `WangGaoXie2023` | Sinkhorn-DRO log-partition duality | `strong_duality`, `sinkhornDual_le_droValue` |
| `Drsb` | Evaluation-card capstone | `wdrsb_cost_bound`, `sdrsb_cost_bound` |

Each paper-facing declaration should identify its source theorem, proposition, equation,
or explicitly state that the Lean proof follows a different route.

## Two independent Birkhoff--Hopf proofs

The finite positive-kernel contraction theorem is formalized twice intentionally.

1. [`ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean`](ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean)
   contains a short AI-discovered Doeblin/weighted-average proof. It normalizes weighted
   sums, turns pairwise cross-ratio bounds into pointwise comparisons, and finishes with a
   scalar logarithmic estimate. It is **not** Carroll's linear-programming reduction.
2. [`ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/`](ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/)
   follows the Eveson--Nussbaum cone/2-dimensional-subspace route and reaches the sharper
   coefficient.

This proof pluralism is a research feature: an independently discovered machine-assisted
argument can be compared against a proof that tracks published human reasoning. Refactors
may share definitions and elementary lemmas, but neither route should call the other
route's hard contraction theorem.

## Layout

```text
.
├── ForMathlib.lean / ForMathlib/     # reusable paper-agnostic results
├── <Paper>.lean / <Paper>/           # source-facing libraries
├── Drsb.lean / Drsb/                 # card capstone
├── Challenge/                        # Mathlib-only challenge specs and project-backed solutions
├── comparator/                       # comparator configurations
├── scripts/                          # validation and audit helpers
├── prose/                            # source-oriented mathematical transcriptions
├── audits/                           # dated structural audits
├── formalization.yaml               # source/result metadata
├── STATUS.md                         # dated checked state
└── PROOF_PIPELINE.md                 # current work queue
```

`Challenge/**/Conformance.lean` intentionally states challenge leaves with omitted proofs;
the corresponding project proofs live in sibling `Leaderboard.lean` files. Production
proof-source scans should exclude `Challenge/` explicitly.

## Build and checks

The pinned toolchain is recorded in `lean-toolchain`; the Mathlib revision is recorded in
`lake-manifest.json`.

```bash
lake exe cache get
lake build

# Production source scan; Challenge conformance specifications are intentionally excluded.
grep -rn --include='*.lean' \
  --exclude-dir=.lake --exclude-dir=.reference-clones \
  --exclude-dir=reference --exclude-dir=Challenge \
  -w sorry .

# Comparator signature pre-flight.
python3 scripts/check_comparator_signatures.py
```

A build result, source scan, or `#print axioms` report should always be recorded with its
commit, command, and scope. See [`STATUS.md`](STATUS.md).

## Current development priorities

The two card inequalities are not the current proof-development bottleneck. The active
priorities are:

1. improve reusable finite mathematics for upstream contribution, beginning with a staged
   decomposition of `matrix_scaling_exists`;
2. minimize assumptions by adding small `_core` theorems while retaining source-faithful
   wrappers;
3. clarify the production and alternate compactness routes in `ProjectiveLag.lean` without
   deleting useful scaffolding;
4. maintain both independent Birkhoff--Hopf proofs;
5. continue the long-horizon interval-path, KL-exhaustion, Cameron--Martin, and SDE work
   only through mathematically honest interfaces and roadmaps.

The detailed ordering and acceptance checks are in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).
