# AIQ DRSB Formalization

Lean 4 formalization of the mathematical claims underlying the GaTech **DRSB**
(Distributionally-Robust Schrödinger Bridge) TA1 evaluation cards. The repository has
one library per theorem-bearing source paper, a paper-agnostic `ForMathlib` staging
library, a `Drsb` capstone, and source-oriented prose under [`prose/`](prose/).

> **Start with [`AGENTS.md`](AGENTS.md).** It records the project purpose, provenance
> rules, workflow, and known traps. For a dated account of the checked source state,
> read [`STATUS.md`](STATUS.md). Do not infer current status from old journal or planning
> entries.

## The evaluation-card story

The two card-facing declarations are in [`Drsb/Basic.lean`](Drsb/Basic.lean):

- `Drsb.wdrsb_cost_bound` corresponds to `wdrsb_cost_bound.yaml`;
- `Drsb.sdrsb_cost_bound` corresponds to `sdrsb_cost_bound.yaml`.

Both prove a one-sided expectation bound of the form

```text
E_mu[V] <= a Wasserstein- or Sinkhorn-DRO dual worst-case bound,
```

for a source distribution `mu` in the relevant ambiguity ball. At this boundary the
value function `V : X -> R` is abstract. Its intended Schrödinger-bridge / stochastic-
control interpretation comes from Chen--Georgiou--Pavon, but constructing that `V` from
continuum SDE data is not a proof-term dependency of either card theorem.

The card claims are specializations of published DRO results rather than verbatim
statements from a single DRSB paper:

| Card theorem | Published backing | Relationship |
|---|---|---|
| `Drsb.wdrsb_cost_bound` | Blanchet--Murthy (2019); Gao--Kleywegt (2023) | quadratic-cost Wasserstein-DRO specialization and weak-duality consequence |
| `Drsb.sdrsb_cost_bound` | Wang--Gao--Xie, *Sinkhorn Distributionally Robust Optimization* (Operations Research, 2025) | Sinkhorn-DRO log-partition specialization and weak-duality consequence |
| interpretation of `V` | Chen--Georgiou--Pavon (2021) | mathematical provenance; abstract at the card-theorem boundary |

The shortest description of the formal argument is:

1. assume `mu` belongs to the stated Wasserstein or Sinkhorn ambiguity set;
2. apply the appropriate weak-duality inequality to the abstract objective `V`;
3. specialize the published dual expression to quadratic transport cost;
4. conclude that `E_mu[V]` is bounded by the card's robust dual value.

The source-faithful strong-duality and worst-case-optimizer developments are valuable
parallel formalizations. They are not dependencies of the two card inequalities unless a
specific declaration says otherwise. Exact source anchors and fidelity notes are collected
in [`LITERATURE_REFERENCES.md`](LITERATURE_REFERENCES.md).

## Notable reusable formalization

The card capstones are small because they sit on a much broader body of reusable work.
The following are the most substantial theorem families developed in this repository.
They are staged in `ForMathlib` when paper-agnostic and wrapped in paper namespaces when
source-facing.

### General Wasserstein-DRO strong duality

[`ForMathlib/OptimalTransport/`](ForMathlib/OptimalTransport/) proves the hard reverse
inequality

```lean
ForMathlib.OT.dualValue_le_droValue
```

from measurable approximate maximizers, concavity of the transport-budget value function,
and existence of a nonnegative supergradient. This avoids taking the duality gap or an
attaining worst-case measure as a primitive assumption. Source-facing consequences include
`GaoKleywegt2023.strong_duality_thm1_of_regularity`,
`BlanchetMurthy2019.wdro_strong_duality`, and
`Drsb.wdrsb_strong_duality_of_regularity`.

Published baselines: Blanchet--Murthy, Theorem 1; Gao--Kleywegt, Theorem 1. The Lean proof
uses an independent epsilon-argmax / supergradient route rather than reproducing the papers'
full minimax architecture.

### Sinkhorn-DRO duality and Gibbs laws

[`WangGaoXie2023/Basic.lean`](WangGaoXie2023/Basic.lean) formalizes the entropic-DRO
log-partition machinery, including

```lean
WangGaoXie2023.sinkhorn_cost_bound
WangGaoXie2023.sinkhornDual_le_droValue
WangGaoXie2023.strong_duality
WangGaoXie2023.exists_worstCase_gibbs
```

The development includes an `ENNReal`-valued Sinkhorn objective, disintegration and
conditional-KL arguments, Gibbs tilting, strong duality under the stated interiority
condition, and construction of worst-case exponential-tilt laws.

Published baseline: Wang--Gao--Xie, Theorem 1, Remark 4, and the associated supplement
lemmas. The stable Lean namespace retains the paper's prepublication year even though the
final journal publication is 2025.

### Donsker--Varadhan and KL infrastructure

[`ForMathlib/MeasureTheory/DonskerVaradhan.lean`](ForMathlib/MeasureTheory/DonskerVaradhan.lean)
proves the Gibbs variational formula and tilted-measure attainment, including

```lean
ForMathlib.MeasureTheory.integral_le_klDiv_add_log_integral_exp
ForMathlib.MeasureTheory.log_integral_exp_eq_sSup
ForMathlib.MeasureTheory.entropic_gibbs_attained_tilted
```

The surrounding KL library also proves convexity, data processing, real-valued finite-KL
wrappers, and the conditional/disintegration identity

```lean
ForMathlib.MeasureTheory.klDiv_compProd_eq_lintegral
```

for product measures with kernels. These results support the Sinkhorn-DRO proofs but are
independently useful probability and information-theory infrastructure.

Classical references include Donsker--Varadhan and the Gibbs variational treatment in
Dupuis--Ellis; see the exact-reference ledger in
[`LITERATURE_REFERENCES.md`](LITERATURE_REFERENCES.md).

### Finite matrix scaling and Sinkhorn convergence

[`ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean`](ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean)
proves

```lean
ForMathlib.matrix_scaling_exists
```

for a strictly positive finite kernel with prescribed positive marginals. The proof uses a
log-domain convex minimization argument and first-order conditions.

The Chen--Georgiou--Pavon finite development then culminates in

```lean
ChenGeorgiouPavon2021.sinkhorn_iterates_converge_to_potentials
```

with positivity, gauge normalization, compactness, cluster-point equations, fixed-point
uniqueness, and projective contraction represented explicitly.

Published comparison sources: Sinkhorn (1964), Sinkhorn--Knopp (1967), and
Franklin--Lorenz (1989). The repository's existence proof and proof organization are not
claimed to be verbatim ports of those papers.

### Two independent Birkhoff--Hopf proofs

The finite positive-kernel contraction theorem is formalized twice intentionally:

```lean
ForMathlib.Matrix.positive_kernel_birkhoff_hopf_contraction
ForMathlib.Matrix.BirkhoffHopf.PaperRoute
  .positive_kernel_birkhoff_hopf_contraction_paper_route
```

1. [`BirkhoffHopf.lean`](ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean) contains an
   AI-discovered Doeblin/weighted-average proof. It normalizes weighted sums, turns pairwise
   cross-ratio bounds into pointwise comparisons, and finishes with a scalar logarithmic
   estimate. It is **not** Carroll's linear-programming reduction.
2. [`BirkhoffHopf/PaperRoute/`](ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/)
   follows the Eveson--Nussbaum cone and two-dimensional-subspace architecture, including
   their sharper two-dimensional coefficient.

This proof pluralism is a research feature: an independently discovered machine-assisted
argument can be compared against a proof that tracks published human reasoning. Refactors
may share definitions and elementary lemmas, but neither route should call the other route's
hard contraction theorem.

Published references: Birkhoff (1957), and S. P. Eveson and R. D. Nussbaum,
*An Elementary Proof of the Birkhoff--Hopf Theorem*, Mathematical Proceedings of the
Cambridge Philosophical Society 117(1):31--55, 1995. Modernized source notes are under
[`prose/distilled_literature/`](prose/distilled_literature/).

### Gaussian Cameron--Martin and energy identities

The repository builds from the finite-dimensional shifted-Gaussian KL identity to original
Euler--Maruyama and infinite-sequence results. Representative declarations include

```lean
ForMathlib.MeasureTheory.klDiv_emShift_eq_emEnergy
ForMathlib.MeasureTheory.klDiv_stdSeqGaussian_map_add_dichotomy
ChenGeorgiouPavon2021.energy_identity_euler_maruyama
ChenGeorgiouPavon2021.energy_identity_sequenceModel
```

The sequence result captures the Cameron--Martin/Kakutani finite-versus-infinite KL
dichotomy for deterministic shifts. The continuum SDE/Girsanov identification is a separate,
longer-horizon development and should not be inferred from the sequence-model theorem.

Published mathematical references include Cameron--Martin (1944), Kakutani (1948), and
Girsanov (1960). The finite Gaussian theorem-code provenance is recorded separately below.

### Schrödinger bridge, stochastic control, and entropic OT assembly

[`ChenGeorgiouPavon2021/`](ChenGeorgiouPavon2021/) also contains source-facing assembly
results such as

```lean
ChenGeorgiouPavon2021.schrodingerBridge_KL_eq_SOC
ChenGeorgiouPavon2021.dynamic_eq_static_SB
ChenGeorgiouPavon2021.staticSB_eq_entropicOT
ChenGeorgiouPavon2021.optimal_control_eq_grad_log
```

These modules formalize substantial parts of the theorem architecture in Chen--Georgiou--
Pavon. Where general continuum SDE, PDE verification, gluing, or optimizer-existence theory
is not yet derived from primitive assumptions, the boundary is represented by explicit
hypotheses or data interfaces. These source-facing assembly results are important, but they
should be distinguished from the fully closed finite and measure-theoretic theorem families
listed above.

## Critical vendored foundations

Published mathematics and vendored theorem code are different forms of provenance. Most
Lean proofs in this repository were developed here while following or comparing against
published sources. The checked source tree has two critical external theorem-code vendoring
points.

### General Kolmogorov extension theorem

The files under [`ForMathlib/KolmogorovExtension/`](ForMathlib/KolmogorovExtension/) are
vendored from:

- Rémy Degenne and Peter Pfaffelhuber,
  [`RemyDegenne/kolmogorov_extension4`](https://github.com/RemyDegenne/kolmogorov_extension4);
- source commit `bb86968580787bfa8024a11b93a26d4c850352b2`;
- Apache-2.0 license;
- retrieved 2026-07-04.

The vendored files provide the general `projectiveLimit` construction and associated
projective-limit properties that were not available in the pinned Mathlib revision. This
foundation is used to construct the concrete nonnegative-time Wiener measure. Adaptations
and additions are marked with `DRSB-CHANGE:` and `DRSB-ADD:` for contribute-back review.
Full provenance and deletion/upstream policy are in
[`ForMathlib/KolmogorovExtension/README.md`](ForMathlib/KolmogorovExtension/README.md).

### Finite-dimensional Gaussian relative entropy

Selected declarations in
[`ForMathlib/MeasureTheory/GaussianEntropy.lean`](ForMathlib/MeasureTheory/GaussianEntropy.lean)
are vendored from:

- Michael R. Douglas,
  [`mrdouglasny/gibbs-variational`](https://github.com/mrdouglasny/gibbs-variational);
- source file `GibbsVariational/GaussianEntropy.lean`;
- source commit `75e08d8aaca83bb090fc43855898991fbfc9abf3`;
- Apache-2.0 license;
- retrieved 2026-07-03.

The vendored portion includes `stdGaussian`, the finite-product Gaussian KL lemmas, and
`klDiv_stdGaussian_map_add`, the identity
`KL(N(h,I) || N(0,I)) = (1/2) ||h||^2`. Only the enclosing namespace was adapted. The
Euler--Maruyama theorem `ForMathlib.MeasureTheory.klDiv_emShift_eq_emEnergy` and the later
sequence/continuum-facing assembly built from this lemma are original developments in this
repository.

The authoritative machine-readable provenance for vendored declarations is in
[`formalization.yaml`](formalization.yaml). File headers retain upstream attribution and
license notices. External package dependencies installed through Lake are separate from
these source-vendored theorem libraries.

## Libraries

| Library | Role | Representative declarations |
|---|---|---|
| `ForMathlib` | Paper-agnostic staging for KL/Donsker--Varadhan, OT/DRO, measurable selection, finite matrix scaling, projective metrics, Gaussian entropy, and continuum support | `log_integral_exp_eq_sSup`, `OT.dualValue_le_droValue`, `matrix_scaling_exists`, `positive_kernel_birkhoff_hopf_contraction` |
| `ChenGeorgiouPavon2021` | SB/SOC/entropic-OT, finite Sinkhorn convergence, and sequence/path-space targets | `schrodingerBridge_KL_eq_SOC`, `sinkhorn_potentials_exist`, `sinkhorn_iterates_converge_to_potentials`, `energy_identity_sequenceModel` |
| `BlanchetMurthy2019` | Wasserstein-DRO source-facing theorems | `wdro_strong_duality` |
| `GaoKleywegt2023` | Wasserstein-DRO duality and worst-case structure | `strong_duality_thm1_of_regularity`, `worstCase_structure_cor1` |
| `MohajerinEsfahaniKuhn2018` | Data-driven Wasserstein-DRO reformulation and structured worst-case laws | `worstCaseExpectation_eq_dual`, `worstCase_exists` |
| `WangGaoXie2023` | Sinkhorn-DRO log-partition duality | `strong_duality`, `sinkhornDual_le_droValue`, `exists_worstCase_gibbs` |
| `Drsb` | Evaluation-card capstone | `wdrsb_cost_bound`, `sdrsb_cost_bound` |

Each paper-facing declaration should identify its source theorem, proposition, equation, or
explicitly state that the Lean proof follows a different route.

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
├── formalization.yaml               # source/result and vendoring metadata
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

# Guard the live documentation against known contradictory status narratives.
python3 scripts/check_documentation_consistency.py
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
