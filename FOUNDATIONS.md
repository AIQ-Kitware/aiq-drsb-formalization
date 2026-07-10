# Foundations and dependency map

This document maps the mathematical layers beneath the DRSB formalization. It is a
navigation aid, not a global completion report. For dated build, source-scan, and named
`#print axioms` observations, use [`STATUS.md`](STATUS.md). For the active refactoring
queue, use [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md).

Gap claims about Mathlib and external Lean projects are dated observations. Re-run the
searches before treating them as current.

## 1. Evaluation-card boundary

The literal evaluation-card theorems are:

- `Drsb.wdrsb_cost_bound`;
- `Drsb.sdrsb_cost_bound`.

Both prove a one-sided robust expectation bound for an abstract objective
`V : X -> R`. Their proof terms do not consume the Chen--Georgiou--Pavon continuum
construction of `V`, the finite Sinkhorn-convergence development, or the source-faithful
MEK/GK worst-case-structure corollaries.

The literature relationship is:

| Card theorem | Published backing | Lean relationship |
|---|---|---|
| `Drsb.wdrsb_cost_bound` | Blanchet--Murthy; Gao--Kleywegt | quadratic-cost Wasserstein-DRO specialization and weak-duality consequence |
| `Drsb.sdrsb_cost_bound` | Wang--Gao--Xie | Sinkhorn-DRO log-partition specialization and weak-duality consequence |
| interpretation of `V` | Chen--Georgiou--Pavon | provenance at the card boundary; `V` remains abstract in the theorem |

The equality and worst-case-law theorems in the paper-facing libraries are valuable
parallel results. They should not be described as dependencies of the two card
inequalities unless an actual declaration reference establishes that dependency.

## 2. Wasserstein-DRO layer

The reusable direction used by the card is the per-coupling Lagrangian inequality:

```text
coupling feasibility
  -> ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost
  -> weak-duality assembly
  -> Drsb.wdrsb_cost_bound
```

The reverse inequality needed for equality is represented in two levels:

- `Drsb.wdrsb_strong_duality` accepts
  `hge : dualValue <= primalValue` explicitly;
- `Drsb.wdrsb_strong_duality_of_regularity` obtains that inequality from the proved
  regularity route in `ForMathlib/OptimalTransport/StrongDualityGe.lean`.

Thus `hge` is neither an unexplained project invention nor a card assumption. It is the
hard direction of the published strong-duality theorem, retained as a useful factored
interface and discharged by a stronger wrapper under explicit hypotheses.

The repository also contains source-facing Gao--Kleywegt and
Mohajerin--Esfahani--Kuhn developments. Their structured worst-case-law conclusions may
retain explicit attainment, measurable-map, or regularity ingredients even when the
card inequality does not need them.

## 3. Sinkhorn-DRO layer

The Sinkhorn card route is:

```text
Donsker--Varadhan / Gibbs variational identity
  -> entropic inner optimization / log partition
  -> Sinkhorn weak duality
  -> Drsb.sdrsb_cost_bound
```

`Drsb.sdrsb_strong_duality` does not take an `hge` argument. It uses the repository's
Sinkhorn strong-duality theorem under an explicit Slater/interiority hypothesis.
`Drsb.sdrsb_strong_duality_of_radius_gt_independent_cost` supplies a concrete sufficient
radius condition. The source paper also treats the boundary case; formalizing that
limiting argument remains a source-fidelity extension rather than a card blocker.

The namespace `WangGaoXie2023` is a stable historical identifier based on the
pre-publication version. The final Operations Research publication is from 2025.

## 4. Finite matrix scaling and Sinkhorn convergence

### Existence

`ForMathlib.matrix_scaling_exists` proves positive finite matrix scaling by log-domain
convex minimization. `ForMathlib.sinkhorn_potentials_exist` is the corresponding
potential-level wrapper. The current maintenance goal is to decompose the long proof
into reviewable stages without changing its public statement.

### Convergence and proof plurality

The projective-metric development is present in the repository, including the
Franklin--Lorenz route used in finite Sinkhorn convergence. The main remaining work here
is proof organization, assumption minimization, source comparison, and reuse—not an
unproved global convergence claim.

The positive-kernel Birkhoff--Hopf contraction is intentionally formalized twice:

1. `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean` contains an AI-discovered
   Doeblin/weighted-average proof;
2. `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/` follows the
   Eveson--Nussbaum cone and two-dimensional-subspace argument.

The direct proof is not Carroll's linear-programming reduction. Both routes are research
artifacts worth preserving. Shared definitions and elementary lemmas are appropriate,
but neither route's hard contraction theorem should be used to prove the other.

Perron--Frobenius theory and Birkhoff--von Neumann decomposition are useful neighboring
subjects but are not required by the current finite scaling proof.

## 5. Schrödinger bridge, stochastic control, and continuum work

The card theorems take `V` abstractly, so this layer is not load-bearing for the literal
card inequalities. It remains important for the secondary goal of formalizing the
published SB/SOC/entropic-OT theory and building reusable stochastic-analysis results.

Current represented layers include finite Gaussian entropy calculations, sequence-model
Cameron--Martin/Kakutani results, finite Sinkhorn results, and explicit theorem
interfaces for deeper analytic steps. Long-horizon work includes:

- a canonical interval path carrier;
- dyadic filtration generation on that carrier;
- KL exhaustion along finite projections;
- Cameron--Martin quasi-invariance for path measures;
- conditional Girsanov and the continuous control-energy identity;
- source-faithful HJB/Hopf--Cole verification under stable analytic assumptions.

When a target statement is not stable—especially while the path carrier is known to be
provisional—record it in a roadmap rather than introducing a theorem whose proposition
does not express the named mathematics. Introduce Lean interfaces when they have a real
client, package meaningful verification data, or correspond to a stable source theorem.

## 6. Mathlib and external-proof mining

The dated external survey lives in [`SURVEY_LEADS.md`](SURVEY_LEADS.md). In particular:

- Mathlib has Sion's minimax theorem;
- the repository supplies several reusable KL/Donsker--Varadhan, measurable-selection,
  OT/DRO, matrix-scaling, and projective-metric results not found in the pinned Mathlib;
- external Perron--Frobenius and finite entropic-OT developments are relevant comparison
  points but do not replace the two Birkhoff routes in this repository;
- stochastic integration, SDE, and Girsanov infrastructure remains a long-horizon area.

Before adapting an external proof, record its author, exact commit, file permalink,
license, retrieval date, and the extent of the adaptation.

## 7. Challenge harness

`Challenge/**/Conformance.lean` contains Mathlib-only specifications with intentionally
omitted proofs. Project-backed solutions live in the corresponding `Leaderboard.lean`
files. Any dependency report should name the exact declaration and command; it should
not be generalized to an entire directory or repository.

A typical upstream workflow is:

1. state a Mathlib-only leaf in `Conformance.lean`;
2. compare independent project-backed candidates in `Leaderboard.lean`;
3. inspect the named declaration's dependencies;
4. move the selected proof into a focused `ForMathlib` module;
5. preserve provenance and source-facing wrappers.
