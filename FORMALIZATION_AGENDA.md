# Formalization agenda for a full distributionally robust Schrodinger bridge theory

This document is the strategic roadmap for taking the repository beyond the two evaluation-card
inequalities and toward a reusable, maximally strong theory of distributionally robust
Schrodinger bridges.

It is deliberately broader than `PROOF_PIPELINE.md`:

- `PROOF_PIPELINE.md` is the ordered queue for small, immediately actionable proof and refactoring
  overlays.
- this document defines the long-term theorem architecture, package boundaries, north-star
  statements, and the order in which foundational theories should be completed.

The repository must continue to obey the honesty rule in `AGENTS.md`: package scaffolding may define
stable import boundaries and documentation, but it must not introduce theorem-shaped placeholders,
`True` conclusions, or structures whose fields merely restate the desired theorem.

## 1. Strategic decision

The card theorems are complete enough to serve their original purpose. The next level is not another
paper-specific wrapper. It is a theory-first architecture in which:

1. information theory, transport, entropic transport, path-space probability, stochastic control,
   Schrodinger bridges, and DRO have stable paper-neutral import boundaries;
2. the current paper libraries become provenance-preserving source wrappers over reusable results;
3. the final robust-bridge theorems construct the objective from a concrete bridge/control model
   instead of accepting an arbitrary `V : X -> R`;
4. strong duality, optimizer existence, optimizer structure, and approximation theorems are exposed
   separately rather than compressed into one oversized capstone;
5. all infinite-cost phenomena are represented in an extended-real type until finiteness has been
   proved, so no bad branch silently becomes zero.

The new `DrsbTheory` module hierarchy is a transition layer. It gives downstream work stable imports
now, while implementations can move out of paper namespaces one theorem family at a time.

## 2. The north-star theorem ladder

The strongest useful result is not a single theorem. It is a ladder whose lower rungs remain reusable
without the upper ones.

### N0. Honest robust expectation bounds

For a measurable objective with explicit growth/integrability assumptions and a source law in an
honestly defined ambiguity set:

- prove the one-sided Wasserstein and entropic robust expectation bounds;
- use extended-real transport costs so ambiguity-set membership itself excludes infinite-cost junk;
- recover the existing real-valued card theorems as compatibility corollaries.

### N1. Strong DRO duality and optimizer structure

Under minimal topological and coercivity assumptions:

- identify the robust primal value with the scalar dual value;
- prove existence of an optimal multiplier when it is mathematically available;
- prove existence of a worst-case law under compactness/tightness hypotheses;
- characterize worst-case laws by measurable transport selectors or Gibbs kernels;
- include boundary cases such as the zero-multiplier essential-supremum endpoint rather than deleting
  them from the dual domain.

### N2. Concrete Schrodinger bridge value theory

For a concrete reference Markov law and endpoint marginals:

- prove existence and uniqueness of the static entropy minimizer;
- prove the product-potential/Schrodinger-system characterization;
- prove equality of static entropy, dynamic path-space entropy, stochastic-control energy, and
  entropic-OT values;
- prove existence of the controlled bridge and identify its endpoint law;
- state gauge uniqueness separately from optimizer uniqueness.

### N3. Concrete stochastic-control value function

For a controlled diffusion on a canonical interval path space:

- construct the controlled path law;
- prove the Girsanov/Cameron-Martin energy identity;
- prove the dynamic programming principle and a verification theorem;
- identify the value function with a Hopf-Cole/Feynman-Kac expression under appropriate regularity;
- identify the optimal feedback control where differentiability permits it.

This rung replaces the abstract `V` at the card boundary by a proved object.

### N4. End-to-end robust bridge equality

For the concrete bridge value function from N3 and either a Wasserstein or entropic ambiguity set on
the initial law:

- identify the robust bridge value with the corresponding DRO dual;
- show every admissible source law satisfies the certified cost bound;
- prove attainment by a worst-case source law when the hypotheses support it;
- compose the worst-case source law with an optimal bridge/control law;
- distinguish a max-min value theorem from a genuine saddle theorem, and prove interchange only from
  an explicit minimax result.

The result should expose both the source-law optimizer and the bridge/control optimizer. It should
not merely restate `expect mu V <= bound` with `V` abstract.

### N5. Approximation, computation, and stability

Relate the ideal theorem to finite algorithms:

- convergence of finite-grid path laws and energies to the continuum model;
- convergence of finite Sinkhorn/IPF iterates to Schrodinger potentials;
- convergence of discrete entropic transport values to the continuum value;
- stability of robust values and optimizers under perturbations of marginals, costs, radii, and
  regularization;
- explicit error decomposition for time discretization, finite sampling, truncated optimization,
  and approximate potentials.

This is the layer that can eventually turn the current informal "formalization edges" into proved
quantitative approximation edges.

## 3. Theory package dependency graph

The package boundaries are intentionally mathematical rather than paper-based.

```text
DrsbTheory.Information
        |
        +----------------------+
        |                      |
DrsbTheory.Transport     DrsbTheory.PathSpace
        |                      |
DrsbTheory.EntropicTransport   DrsbTheory.StochasticControl
        |                      |
        +---------- DrsbTheory.SchrodingerBridge
                              |
DrsbTheory.DRO ----------------+
                |
        DrsbTheory.RobustBridge
```

The graph is not a claim that every imported implementation is already paper-neutral. It is the
migration target and stable downstream import surface.

## 4. Package contracts

### 4.1 `DrsbTheory.Information`

Scope:

- KL divergence in `ENNReal` and finite real wrappers;
- absolute continuity and Radon-Nikodym identities;
- convexity, lower semicontinuity, data processing, and chain rules;
- conditional/disintegrated KL;
- Donsker-Varadhan/Gibbs variational principles;
- exponential tilting and measurable kernels;
- entropy exhaustion along increasing sigma-algebras.

Current assets:

- Donsker-Varadhan primal and dual families;
- KL convexity and data processing;
- product-kernel chain rule;
- tilted measures/kernels;
- Gaussian and sequence Cameron-Martin entropy results.

Major missing theory:

- a systematic extended-real API that avoids premature `toReal`;
- general conditional entropy and filtration exhaustion theorems;
- lower-semicontinuity/topology results packaged for compactness arguments;
- equality/strict-convexity results strong enough to yield optimizer uniqueness cleanly.

### 4.2 `DrsbTheory.Transport`

Scope:

- couplings and marginals on two possibly different spaces;
- nonnegative extended-real transport costs;
- Kantorovich primal values and attainment;
- measurable transport selectors;
- Kantorovich duality;
- Wasserstein costs, balls, topology, tightness, and moment transfer;
- transport-based DRO weak and strong duality.

Current assets:

- coupling construction and convexity;
- near-optimal plan extraction for the current real-valued infimum;
- measurable epsilon-argmax machinery;
- a complete converse-Lagrangian/supergradient route for real-valued WDRO duality.

First critical gap:

The current `otCost` and `W2sq` are real-valued Bochner-integral infima. Nonintegrable costs can
therefore enter through a junk zero branch, forcing explicit second-moment hypotheses on both laws.
The first new proof program should introduce the canonical `ENNReal` Kantorovich value and a
Wasserstein ball defined from it, prove compatibility with the old real value under finiteness, and
move the primary WDRSB theorem to the honest ball.

Major later gaps:

- primal attainment from lower semicontinuity and tightness;
- full Kantorovich duality in the generality needed by the project;
- Wasserstein topology and compactness of moment-bounded sets;
- unbounded objectives controlled by growth conditions rather than global boundedness.

### 4.3 `DrsbTheory.EntropicTransport`

Scope:

- entropy-regularized transport with external reference measures;
- the classical Schrodinger problem relative to a reference coupling or Markov law;
- entropic cost versus debiased Sinkhorn divergence, kept as distinct definitions;
- dual potentials, Gibbs kernels, and optimizer characterization;
- finite matrix scaling and continuous-space analogues;
- Sinkhorn/IPF convergence and quantitative contraction.

Current assets:

- an honest `ENNReal` entropic objective;
- Sinkhorn-DRO weak/strong duality under interiority;
- Gibbs worst-case kernels;
- rectangular positive matrix scaling;
- finite Schrodinger potentials and Sinkhorn convergence;
- two independent finite Birkhoff-Hopf contraction proofs.

Major missing theory:

- the zero-multiplier/essential-supremum endpoint;
- boundary strong duality without strict Slater when the source theorem supports it;
- general-space existence and uniqueness of entropic transport optimizers;
- a clean distinction and relation between regularized transport cost and debiased Sinkhorn
  divergence;
- continuous-kernel Sinkhorn/IPF convergence and stability.

### 4.4 `DrsbTheory.PathSpace`

Scope:

- canonical continuous paths on a compact interval;
- evaluation maps, endpoint maps, and generated Borel sigma-algebras;
- filtrations and finite-grid projections;
- Wiener and more general Markov reference measures;
- regular conditional laws and path disintegration;
- Cameron-Martin quasi-invariance;
- KL exhaustion and path-space entropy limits.

Current assets:

- vendored Kolmogorov extension;
- Wiener measure and finite-dimensional Gaussian projective laws;
- path embeddings into countable coordinates;
- sequence Gaussian Cameron-Martin/Kakutani theory;
- finite dyadic and interval-path infrastructure;
- honest interfaces for the remaining continuum closure.

Major missing theory:

- settle the canonical anchored continuous interval path carrier and migrate clients;
- prove dyadic/rational evaluations generate its Borel sigma-algebra;
- prove the required KL exhaustion theorem on that carrier;
- prove Cameron-Martin quasi-invariance rather than accepting absolute continuity as a field;
- package conditional path kernels and Markov bridges.

### 4.5 `DrsbTheory.StochasticControl`

Scope:

- controlled SDE/path-law construction;
- admissible controls and finite-energy classes;
- Girsanov and control-energy identities;
- dynamic programming;
- HJB, Feynman-Kac, and Hopf-Cole verification;
- existence and characterization of optimal controls.

Current assets:

- abstract `SBData`, feasibility, energy, and value definitions;
- finite Euler-Maruyama energy identity;
- sequence-model energy identity;
- non-circular data interfaces for disintegrated continuum energy assembly.

Major missing theory:

- a concrete controlled diffusion model rather than an arbitrary `pathLaw` field;
- stochastic integration and Girsanov on the chosen path carrier;
- admissibility/uniqueness results for controlled laws;
- source-faithful dynamic programming and PDE verification;
- enough regularity to construct the value function and optimal feedback used by DRSB.

### 4.6 `DrsbTheory.SchrodingerBridge`

Scope:

- static entropy projection;
- dynamic path-space bridge;
- stochastic-control bridge;
- entropic optimal transport;
- equality of values and transfer of optimizers;
- Schrodinger potentials, factorization, existence, and uniqueness.

Current assets:

- finite matrix/potential existence and convergence;
- static/dynamic/SOC definitions and assembly theorems;
- target interfaces for gluing, strict convexity, and optimizer construction.

Major missing theory:

- construct the reference bridge/gluing kernel on the concrete path model;
- prove entropy disintegration equality at endpoints;
- derive static optimizer existence from compactness/lower semicontinuity or dual potentials;
- prove strict convexity uniqueness under precise absolute-continuity hypotheses;
- transfer the static optimizer to a dynamic controlled bridge.

### 4.7 `DrsbTheory.DRO`

Scope:

- robust expectations over abstract ambiguity sets;
- Wasserstein, entropic, and eventually other divergence/transport balls;
- weak duality, strong duality, attainment, and optimizer structure;
- radius sensitivity, monotonicity, concavity, and sub/supergradients;
- data-driven and empirical reformulations.

Current assets:

- Wasserstein weak and strong duality;
- entropic/Sinkhorn weak and strong duality;
- worst-case Gibbs laws;
- source-facing Gao-Kleywegt and Mohajerin-Esfahani-Kuhn results.

Major missing theory:

- unbounded objective classes with coercive growth assumptions;
- compactness and worst-case-law attainment from primitive hypotheses;
- a common theorem interface shared by Wasserstein and entropic ambiguity models;
- sensitivity and stability of the robust value;
- empirical convergence/concentration results separated from deterministic duality.

### 4.8 `DrsbTheory.RobustBridge`

Scope:

- compose the concrete bridge value with the DRO layer;
- expose end-to-end robust value equalities and optimizer statements;
- connect continuum, finite approximation, and card-level compatibility results.

Current assets:

- the two abstract-objective card bounds;
- Wasserstein and entropic strong-duality wrappers;
- a terminal log-partition expression;
- provenance imports from the bridge/control theory.

Major missing theory:

- replace abstract `V` with the value function constructed by `StochasticControl`;
- prove the robust value is the supremum of concrete bridge values over source laws;
- compose worst-case source laws with optimal controlled bridges;
- formulate and prove max-min or saddle results with the quantifier order made explicit;
- prove approximation and stability corollaries suitable for evaluation code.

## 5. Ordered program

### Phase A. Architecture and ratchets

Status after the scaffold overlay:

- establish the `DrsbTheory` import hierarchy;
- add this agenda;
- keep all existing public declarations unchanged;
- add no theorem-shaped placeholders;
- include the new agenda in documentation consistency checks.

Acceptance:

- every new root module imports only lower layers or current implementation modules;
- `lake build DrsbTheory` succeeds;
- the full build remains green;
- documentation and non-vacuous-scaffold ratchets pass.

### Phase B. Honest extended-real Kantorovich theory

This is the immediate next proof phase.

1. Add an `ENNReal` coupling cost for nonnegative measurable costs without passing through
   `ENNReal.ofReal` when a native `ENNReal` cost is available.
2. Define an `ENNReal` Kantorovich primal infimum.
3. Prove nonemptiness of couplings and basic monotonicity/nonnegativity.
4. Define the honest quadratic Wasserstein cost and ambiguity ball.
5. Prove that finite honest cost yields the moment/integrability facts needed by the real dual
   integrals.
6. Prove compatibility with the existing `otCost`/`W2sq` under explicit finiteness.
7. Restate the primary WDRSB bound on the honest ball and derive the old theorem as a compatibility
   wrapper where possible.

Do not begin by deleting the old API. Land the new theory beside it, migrate clients, then deprecate
or narrow the compatibility layer.

### Phase C. Full robust expectation theory

1. Generalize the weak-duality kernel to unbounded objectives with explicit positive/negative-part
   hypotheses.
2. Package measurable epsilon-argmax and supergradient results into a reusable strong-duality
   theorem.
3. Prove primal attainment under lower semicontinuity, coercivity, and tightness.
4. Prove worst-case-law structure and multiplier complementary slackness.
5. Add sensitivity in the radius and cost/objective perturbations.

### Phase D. Complete entropic transport and Sinkhorn DRO

1. Encode the zero-multiplier endpoint by an essential-supremum convention.
2. Close the source-faithful boundary strong-duality case.
3. Prove general optimizer existence/uniqueness for the entropic transport problem.
4. Separate regularized transport cost from debiased Sinkhorn divergence and prove the relation
   needed by any card/model that truly uses the latter.
5. Generalize finite convergence results toward positive kernels on compact/standard Borel spaces.

### Phase E. Canonical path-space probability

1. Freeze the anchored continuous interval path carrier.
2. Prove its measurable/topological API and dyadic generation.
3. transport Wiener measure to that carrier;
4. prove KL exhaustion along the finite-grid filtration;
5. prove Cameron-Martin quasi-invariance and density formulas;
6. package conditional reference bridge kernels.

### Phase F. Controlled diffusion and value-function construction

1. Define the concrete controlled diffusion/path-law model.
2. Prove finite-energy absolute continuity and Girsanov.
3. prove the continuum control-energy/KL identity;
4. prove dynamic programming and verification;
5. construct the value function and optimal control under clearly separated regularity tiers.

### Phase G. Full Schrodinger bridge theory

1. Prove static optimizer existence and uniqueness.
2. Prove product-potential characterization.
3. prove dynamic/static equality by reference-bridge gluing and data processing;
4. prove SOC/entropy equality from Girsanov;
5. transfer optimizers among all formulations.

### Phase H. Robust bridge composition

1. Define robust bridge values with the quantifier order explicit.
2. identify the inner bridge value with expectation of the concrete value function;
3. apply Wasserstein or entropic DRO equality;
4. prove worst-case source-law existence and structure;
5. compose source and control optimizers;
6. prove max-min interchange only under a separately stated minimax theorem.

### Phase I. Approximation and evaluation edges

1. finite-time/grid approximation of controlled path laws;
2. convergence of energies and bridge values;
3. finite Sinkhorn iteration error bounds;
4. empirical ambiguity-set approximation;
5. an end-to-end theorem that bounds the difference between the mathematical robust value and the
   quantity computed by the evaluation pipeline.

## 6. Parallel work lanes

The agenda supports parallel agents without letting them invent disconnected theorem islands.

- Lane T: extended-real transport and WDRO.
- Lane E: entropy, entropic transport, and Sinkhorn DRO endpoints.
- Lane P: path carrier, Wiener measure, filtrations, and KL exhaustion.
- Lane S: stochastic control, Girsanov, and verification.
- Lane B: static/dynamic Schrodinger bridge existence and optimizer transfer.
- Lane R: robust-bridge capstones and approximation edges, consuming only stable lower-layer APIs.

A lane may add a stable interface only when a current client consumes it or the proposition is fixed
by a named mathematical theorem. Otherwise the obligation belongs in this document.

## 7. Definition and theorem design rules

1. Keep infinite values in `ENNReal` until finiteness is proved.
2. Separate an objective value theorem from attainment and from optimizer characterization.
3. Separate existence, uniqueness, and gauge uniqueness.
4. Separate weak duality from strong duality and strong duality from boundary closure.
5. State quantifier order explicitly in every robust-control theorem.
6. Use two-space transport definitions; specialize to a single normed space only for Wasserstein
   geometry.
7. Prefer growth/coercivity assumptions over global boundedness when the proof infrastructure is
   ready.
8. Keep source-paper wrappers, but put reusable mathematical cores in paper-neutral modules.
9. Preserve independent proof routes when they provide meaningful research comparison.
10. Do not make the final capstone depend on finite Sinkhorn convergence unless it is an algorithmic
    approximation theorem; existence/value theorems and iterative convergence are different layers.

## 8. Immediate next overlay after this scaffold

Create the first real `DrsbTheory.Transport` implementation module for the extended-real
Kantorovich layer. The target should be a small vertical slice, not a renaming-only refactor:

- canonical nonnegative `ENNReal` coupling cost;
- canonical `ENNReal` optimal transport cost;
- product-coupling finiteness and diagonal zero-cost lemmas;
- honest quadratic Wasserstein ball;
- a compatibility theorem with the current real-valued cost under integrability;
- at least one migrated WDRSB helper proving that honest ball membership supplies the finite-cost
  edge currently carried as a separate hypothesis.

That overlay should preserve the existing card theorem while introducing a stronger sibling theorem.
Only after the stronger theorem is stable should the old real-valued ball become a compatibility API.
