# PROOF_PIPELINE.md — current proof and upstreaming work queue

This file is the live work plan. It is not a historical ledger. Put completed-session narrative in
[`JOURNAL.md`](JOURNAL.md), dated build/dependency observations in [`STATUS.md`](STATUS.md), and
evergreen rules in [`AGENTS.md`](AGENTS.md).

## 1. Project priorities

Work is selected against two goals:

1. **Primary:** maintain a clear formal correspondence between the two evaluation-card claims and
   their published DRO foundations.
2. **Secondary:** develop reusable formalizations of the underlying mathematics for contribution to
   Mathlib or another curated proof collection.

The two card declarations are already present:

```lean
Drsb.wdrsb_cost_bound
Drsb.sdrsb_cost_bound
```

Neither depends on the continuum path-space campaign, the Birkhoff--Hopf development, or the
source-faithful MEK/GK worst-case-structure theorems. Current proof work should therefore be chosen
mainly by upstream mathematical value and clarity rather than by an imagined card-path emergency.

## 2. Invariants for every overlay

### 2.1 One conceptual change per overlay

Do not combine theorem statement changes, proof decomposition, file moves, and broad documentation
rewrites in one patch. A safe progression is:

1. add a new lemma or truthful interface;
2. prove it and build the narrow file;
3. migrate internal clients;
4. preserve a compatibility/source-facing wrapper;
5. only then consider moving files or deleting obsolete adapters.

### 2.2 Preserve proof pluralism

The finite positive-kernel Birkhoff--Hopf theorem has two intentional routes:

- `BirkhoffHopf.lean`: AI-discovered Doeblin/weighted-average proof;
- `BirkhoffHopf/PaperRoute/*`: Eveson--Nussbaum source-faithful proof.

Shared definitions and elementary metric lemmas are appropriate. The hard theorem of either route
must not become a dependency of the other route. The direct proof is not Carroll's linear-programming
reduction; do not rename or document it as such.

### 2.3 Preserve useful scaffolding

Before deleting a suspicious theorem or adapter:

```bash
rg -n '\bTHEOREM_NAME\b' --glob '*.lean' .
```

Classify every hit as declaration, proof client, documentation, or aggregate exposure. Keep an
alternate proof route or future-theory scaffold when it records genuine mathematical structure.
Delete theorem-shaped markers only when their proposition carries no content and their intended
target is represented in a roadmap or a stable replacement interface.

### 2.4 Report evidence with scope

Use exact commands and named declarations:

```bash
lake env lean path/to/File.lean
lake build Relevant.Library
lake build
```

For theorem dependencies, record the literal `#print axioms` output for the named declaration.
Production source scans must explicitly exclude `Challenge/`, whose conformance files intentionally
state admitted specifications.

## 3. Ordered work queue

### A0. Documentation consistency

**Purpose:** keep readers from following stale dependency maps or obsolete proof-frontier claims.

Required state:

- `README.md`, `STATUS.md`, `AGENTS.md`, `prose/README.md`, and `formalization.yaml` agree on the two
  card declarations and their literature mapping;
- the card inequalities are distinguished from strong-duality equality and worst-case-structure
  theorems;
- the abstract `V` boundary is explicit;
- `hge` is described accurately: present in the factored Wasserstein assembly theorem, discharged by
  a regularity wrapper, absent from both card theorems and from Sinkhorn strong duality;
- both Birkhoff routes are described as a feature;
- no live document describes Sinkhorn convergence as unfinished;
- status statements name their command, commit, and scope.

This overlay should change documentation only.

### A1. Decompose `matrix_scaling_exists`

**Target:** `ForMathlib.matrix_scaling_exists` in
`ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean`.

**Why first:** it is a substantial, paper-agnostic finite-dimensional theorem with direct upstream
value. The existing proof is long enough that review, maintenance, and assumption minimization are
hard.

#### A1.1 Preserve the public theorem

Do not change the current public signature in the first overlay. Extract lemmas underneath it, then
make the public theorem a short assembly.

#### A1.2 Recommended lemma boundaries

Use the existing proof's internal stages rather than inventing a new argument:

1. **Normalized compact domain**
   - define the positive/simplex-like feasible set used for the logarithmic column variable;
   - prove nonemptiness, closedness where applicable, and compactness of the truncated domain.
2. **Objective continuity and attainment**
   - isolate continuity of
     `psi(b) = sum_i p_i log(sum_j G_ij b_j) - sum_j q_j log b_j`;
   - state the exact compact-domain minimizer theorem.
3. **Boundary exclusion/coercive estimate**
   - package the estimate showing a minimizer cannot lie on a forbidden face because
     `-q_j log b_j` diverges while the positive-kernel term stays controlled;
   - this is the most likely place to need locally increased heartbeat limits.
4. **One-dimensional directional derivative**
   - isolate the derivative along `e_j - e_k`;
   - prove the local-minimum derivative vanishes.
5. **Stationarity equalities**
   - derive equality of the relevant scaled column marginal expressions up to a common multiplier.
6. **Multiplier elimination**
   - use mass conservation `sum p = sum q` to identify the multiplier.
7. **Scaling assembly**
   - define the row and column scaling vectors;
   - prove positivity and both marginal equations.

#### A1.3 Expected Lean friction

- Derivative expressions may become unreadable after extraction. Introduce local abbreviations and
  prove simp lemmas for finite sums before moving the proof body.
- Compactness and boundary estimates may depend on local `let` definitions. First turn each `let`
  into a private `def` or a lemma parameter; do not simultaneously generalize types.
- Avoid global `set_option maxHeartbeats`. Scope it around the boundary or derivative lemma that
  actually needs it.
- If a lemma statement becomes more complicated than the original proof segment, stop and choose a
  smaller boundary.

#### A1.4 Acceptance checks

```bash
lake env lean ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean
lake build ForMathlib
lake build
```

The public theorem type must be unchanged. Record `#print axioms ForMathlib.matrix_scaling_exists`
from rebuilt oleans.

### A2. Minimize assumptions with `_core` theorems

**Purpose:** expose mathematically minimal reusable theorems without erasing paper-facing statement
fidelity.

Start with one theorem family per overlay.

#### A2.1 Franklin--Lorenz geometric bound

Candidate:

```lean
hard_core_franklinLorenz_right_column_pairwise_log_correction_geometric_bound
```

Use `lean_minimal_hypotheses` or manual removal to determine whether box bounds, gauge assumptions,
or `gamma < 1` are needed for the local algebraic conclusion. Add a `_core` theorem containing only
the used assumptions. Keep the existing theorem as a wrapper if its extra assumptions describe the
algorithmic context or match a source statement.

#### A2.2 Weighted-average Birkhoff core

Candidate:

```lean
finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound
```

Test whether the global diameter nonnegativity assumption is derivable or unused. Keep the direct
route independent from `PaperRoute`.

#### A2.3 Pointwise positive-kernel contraction

Candidate:

```lean
positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_apply_hilbert_log_diameter_bound
```

The pointwise proof may require only the explicit cross-ratio/diameter inequality, not a separate
abstract coefficient hypothesis. Put the minimal implication in `_core`; retain a coefficient-based
wrapper for API convenience.

#### A2.4 Procedure

1. copy the current theorem to `<name>_core` without changing the proof;
2. remove one hypothesis at a time;
3. rebuild the leaf file after each removal;
4. make the old theorem `exact <name>_core ...`;
5. migrate only paper-agnostic internal clients;
6. retain source-numbered wrappers when they help literature comparison.

### A3. Clarify the `ProjectiveLag` production route

Static inspection shows a round trip:

1. Franklin--Lorenz proves the relevant spread convergence;
2. convergence is converted to absence of a positive bad subsequence;
3. the absence statement is converted back to convergence.

This is logically valid but obscures which theorem contains the mathematical work.

#### A3.1 Safe correction

- make the production `...tendsto_zero_from_gauge_iterates` theorem invoke the established
  Franklin--Lorenz convergence result directly;
- keep the no-positive-subsequence theorem as a derived corollary or alternate compactness-route
  scaffold;
- change comments that call the derived no-subsequence theorem “the hard core”;
- do not delete generic subsequence lemmas until client searches show they have no independent use.

#### A3.2 Likely friction

The direct theorem may currently inherit convenient variables and positivity facts through the
round-trip wrapper. When replacing the final proof, reuse the exact intermediate theorem invocation
already present in the no-subsequence proof rather than reconstructing all arguments manually.

#### A3.3 Acceptance checks

- the production theorem has a direct dependency path to the Franklin--Lorenz result;
- the no-subsequence theorem still elaborates independently as a corollary;
- no public theorem type changes;
- build the compactness aggregate and the full project.

### A4. Continuum honesty cleanup

Two theorem-shaped markers have conclusions equal to `True`:

```lean
dyadicNormalizedIncrementMap_generates_standardWienerRealPathMeasure
cameronMartinDyadicDensity_uniformIntegrability_of_isCameronMartinPath
```

The current broad path carrier is known to be provisional, and one of the markers has no client while
the other feeds an ignored `True` value. Do not design a premature Lean proposition merely to replace
them.

#### A4.1 Correction

1. confirm clients with `rg`;
2. remove the no-client theorem;
3. remove the ignored `True` argument and its theorem;
4. add precise roadmap prose describing:
   - the intended interval path carrier;
   - dyadic sigma-algebra generation;
   - uniform integrability/density-process closure;
   - prerequisites that are not yet fixed;
5. retain proved finite-grid, sequence-Gaussian, and assembly results.

A stable `def ... : Prop` or `structure ... : Prop` should be added only when a real client consumes
it or the statement no longer depends on a carrier known to be wrong.

### A5. Verification-data interfaces only when demanded

The PDE/SDE wrappers often take hypotheses that state the substantive verification result directly.
That can be an honest interface, but a large structure should not be introduced merely to make a
roadmap executable.

Introduce `...VerificationData` only when:

- multiple theorems consume the same coherent fields;
- the fields correspond to a stable published verification theorem;
- the structure removes duplicated assumptions or prevents mismatched combinations.

Otherwise keep a small `_of_verification` theorem with explicit hypotheses and document that it is an
assembly result, not the missing PDE/SDE proof.

### A6. Longer-horizon upstream and continuum work

After A1--A5:

- migrate the general transport cost to an `ENNReal` foundation if the API disruption is justified;
- prepare Mathlib-shaped PRs for Donsker--Varadhan, KL convexity, supergradient existence,
  measurable epsilon-argmax, matrix scaling, and the projective metric;
- close Wang--Gao--Xie's boundary case if a source-faithful proof is desired beyond Slater;
- develop interval path spaces, KL exhaustion, Cameron--Martin quasi-invariance, and Girsanov only
  with explicit source anchors and dependency choices.

## 4. Overlay handoff template

Every proof overlay should report:

```text
Base commit:
Files changed:
Public theorem types changed: yes/no
New theorem names:
Old theorem wrappers retained:
Targeted commands run:
Full build result:
Named #print axioms output:
Known remaining issue:
Next smallest theorem boundary:
```

For alternate proof routes, also report whether either route acquired a new dependency on the other.
