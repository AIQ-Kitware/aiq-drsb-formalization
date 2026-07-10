# Proof audit and remediation guide — AIQ DRSB formalization

**Statically audited source:** commit `d81468009ef35024fd213686133f38b234ec9054` (`Commit ledger`, 2026-07-10)
**Documentation reconciliation base:** commit `ece61a237bab50ff7eef0d2a94fef651b7b01504` (2026-07-10; no Lean-file changes from the audited source)
**Audit date:** 2026-07-10
**Scope:** theorem fidelity, proof architecture, documentation accuracy, preservation of research scaffolding, and preparation of reusable contributions.

## 1. Project priorities and audit philosophy

This repository has two goals, in this order:

1. **Primary:** formalize the published theorem chain that supports the DRSB evaluation-card claims.
2. **Secondary:** retain and improve reusable formalizations of the underlying mathematics so they can be contributed to Mathlib or another curated proof collection.

The audit therefore does **not** treat shortest code as the only objective. A longer development can be valuable when it:

- follows a published proof closely enough to audit against the source;
- records an independently discovered proof of the same result;
- isolates a useful upstream theorem;
- preserves a precise target interface for later continuum work.

Conversely, a theorem can compile and still deserve correction when its name or documentation suggests more mathematics than its proposition contains.

### 1.1 Status language policy

Do not use completion slogans based on the absence of a particular tactic token. They are imprecise, easy to overread, and distract from the theorem statements.

Report checks as scoped observations instead:

```text
At commit <hash>, command <command> returned <result> over <scope>.
The Challenge conformance files intentionally contain admitted specifications and are outside that scope.
```

Preferred evidence includes:

- `lake build` result;
- the exact files or libraries checked;
- `#print axioms` output for named capstones;
- comparator execution status;
- source scans with their exclusions shown explicitly.

The intentional admissions under `Challenge/**/Conformance.lean` are not defects in the production proof libraries and should not be presented as such.

### 1.2 Non-destructive default

Before changing any suspicious declaration, classify it:

| Class | Meaning | Default action |
|---|---|---|
| **C — card critical** | On the actual proof-term path to `Drsb.wdrsb_cost_bound` or `Drsb.sdrsb_cost_bound` | Preserve public statement and imports; add compatibility wrappers before changing APIs |
| **U — reusable/upstream** | Paper-agnostic theorem intended for Mathlib or a proof collection | Improve statement minimality and proof modularity; preserve source-faithful wrappers separately |
| **R — research route** | Independent proof, alternate derivation, or proof-comparison object | Preserve even if another proof is shorter; document provenance and independence |
| **S — scaffold/interface** | A boundary or roadmap target for mathematics not yet instantiated | Keep the target concept; use a proposition/structure when stable and client-driven, otherwise use dated roadmap prose |
| **H — historical record** | Journal or prior work-plan material | Correct misleading current claims; retain useful history with dates and supersession notes |

Deletion is the last step, not the first. A declaration should be removed only after:

1. repository-wide client search;
2. identification of its class;
3. confirmation that its mathematical target is represented elsewhere;
4. migration of clients;
5. a build and named theorem checks.

## 2. Validation performed

The repository-local helper is:

```bash
python3 scripts/audit_proof_shape.py --top 30 --min-span 20 --show-clients --status-language
```

It heuristically reports:

- large files and declaration spans;
- tactic concentration;
- likely adapters, passthroughs, and theorem-shaped targets;
- approximate repository-wide client counts;
- documentation wording that should be replaced by scoped command/results.

It is not a Lean parser. A hit is a review prompt, never an automatic deletion recommendation.

Static inspection covered **126 Lean files**, **23,468 lines**, and approximately **951 top-level declarations**. A source scan found the admitted tactic token only in the intentional Challenge conformance specifications. The execution environment did not have a working Lake installation and could not fetch Elan, so the original pass did not independently certify the recorded build or axiom reports.

### 2.1 Compiler-backed corrections supplied by the maintainer

After the static pass, a maintainer with the pinned Lean toolchain reported:

- `lake build` completed at commit `d81468009ef35024fd213686133f38b234ec9054`
  with 8761 jobs and zero warnings;
- `#print axioms Drsb.wdrsb_cost_bound` reported only `propext`,
  `Classical.choice`, and `Quot.sound`;
- `#print axioms Drsb.sdrsb_cost_bound` reported the same three dependencies;
- the two card theorems do not consume the Chen--Georgiou--Pavon continuum layer,
  finite Sinkhorn convergence, or the source-faithful MEK/GK worst-case-structure results.

These compiler-backed observations supersede any static wording that treated the continuum,
MEK/GK structure corollaries, or finite Sinkhorn convergence as gates for the literal card
inequalities. Strong-duality equalities and source-faithful optimizer results remain valuable
parallel formalizations, but they must be described separately from the card dependency path.

## 3. Executive conclusions

### 3.1 Preserve the two Birkhoff–Hopf proofs

The repository contains two intentionally different proofs of the same positive-kernel contraction seam:

1. **AI-discovered direct route** in `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean`.
2. **Source-faithful Eveson–Nussbaum route** in `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/*`.

This is a feature and should be documented as a research object: an independently discovered machine-assisted proof beside a formalization that tracks published human reasoning.

A terminology correction matters. The direct proof currently in the Lean file is **not** Carroll's linear-programming reduction. It bypasses that reduction by normalizing to probability weights, summing the pairwise inequality to obtain a Doeblin-type pointwise comparison, deriving two linear inequalities, and finishing with a scalar Möbius/log estimate and weighted AM–GM. Carroll's linear-programming route remains important literature and historical scaffolding, but it is not the implementation of the current direct theorem.

### 3.2 Preserve scaffolding, but make its logical status explicit

The continuum and PDE/SDE target files contain valuable architecture. The problem is not that they exist; the problem is that a few target names are implemented as theorems proving `True` or as wrappers that accept the desired conclusion verbatim.

The correction depends on statement stability:

- use a `def ... : Prop` when the target proposition is mathematically stable and has a real client;
- use a `structure ... : Prop` when an assembly theorem consumes meaningful verification data;
- use an `_of_interface`, `_of_data`, or `_of_verification` theorem for a genuine boundary;
- use a roadmap entry, rather than a premature Lean proposition, when the carrier or intended
  statement is known to be provisional.

In particular, the two current `True` markers should be deleted with their ignored clients and
replaced by roadmap text until the canonical interval-path carrier and density process are stable.
Do not flatten the continuum target modules into comments or delete their finite-dimensional achievements.

### 3.3 Separate production dependencies from alternate proof experiments

`ProjectiveLag.lean` currently proves projective spread convergence via Franklin–Lorenz, derives a no-bad-subsequence corollary, and then derives convergence again from that corollary. The no-subsequence result may be useful scaffolding for an independent compactness proof, but the current comments incorrectly describe it as the hard theorem.

The safe correction is to make the production theorem depend directly on the Franklin–Lorenz result while retaining the no-subsequence theorem as a clearly labeled derived bridge or alternate-route scaffold.

### 3.4 Refactor for reuse without erasing proof provenance

The largest proofs should be decomposed, but route identity must remain visible:

- do not make the direct Birkhoff proof call the paper route;
- do not make the paper route call the direct weighted-average theorem;
- shared definitions and elementary metric lemmas are appropriate;
- the route-specific hard reductions should remain independent.

## 4. Agent operating procedure

A weaker agent should follow this protocol for every correction overlay.

### 4.1 One conceptual change per overlay

Do not combine all of the following in one patch:

- theorem statement changes;
- file moves;
- import rewrites;
- proof compression;
- documentation cleanup.

A safe sequence is:

1. documentation-only correction;
2. add new truthful theorem/interface while preserving old API;
3. migrate internal clients;
4. remove or deprecate obsolete adapter;
5. only then split files.

### 4.2 Record clients before editing

For each declaration `NAME`:

```bash
rg -n '\bNAME\b' --glob '*.lean' .
```

Record whether each hit is:

- declaration;
- proof client;
- docstring/comment;
- aggregate import exposure.

Do not infer client count from the audit script alone.

### 4.3 Preserve public seams

When minimizing assumptions, first add a new theorem:

```lean
theorem theorem_name_core ... := by
  ...

-- Existing paper-facing or compatibility theorem.
theorem theorem_name ... extra_hypotheses ... := by
  exact theorem_name_core ...
```

Migrate internal clients to `_core` only after it builds. Keep a source-numbered wrapper when the extra assumptions mirror the paper statement or make source comparison easier.

### 4.4 Verify at increasing scope

Use the narrowest practical sequence:

```bash
lake env lean path/to/edited/File.lean
lake build Relevant.Library
lake build
```

For capstones and proof routes, add a temporary check file containing `#check` and `#print axioms` for the named declarations, or use the repository's existing audit mechanism.

### 4.5 Stop on semantic uncertainty

If an agent cannot state the intended replacement proposition precisely, it should not delete the scaffold. It should:

- improve the docstring;
- mark the declaration as an interface or adapter;
- add the unresolved statement to the relevant roadmap;
- leave the mathematical target available for a stronger agent.

---

# Remediation tasks

## Resolution status (2026-07-10)

The findings below are preserved as originally written. This section records how each was
resolved; per-task headings also carry a short `**Resolution:**` line. The historical
observations are **not** rewritten. See `REMEDIATION_PLAN_2026-07-10.md` for the full
execution log.

- **P2 / Overlay A1 — decompose `matrix_scaling_exists`.** Resolution: completed in
  `3791d88` (M1/M2), `1c9054b` (M3a), `3ba1d17` (M4a/M4b), `36265ff` (M4c/M4d).
  Implementation: `matrix_scaling_exists` became a **47-line assembly over eight private
  lemmas**; public statement byte-for-byte unchanged. Deviations from the recommendation:
  (i) **M3a did not require marginal positivity** — `p`, `q` enter only as coefficients, so
  no `hp`/`hq` were needed; (ii) **M4c required `0 ≤ δ`** for its chosen unit-ball
  boundedness proof (a genuine hypothesis of that lemma's approach, not of the theorem);
  (iii) the **`maxHeartbeats 1000000` override became unnecessary** and was removed — the
  module compiles under default heartbeats. Validation: `lake env lean` exit 0; full build
  8761 jobs exit 0; `#print axioms` `[propext, Classical.choice, Quot.sound]`.
- **A1 (task) / Overlay A2 — minimize reusable theorem assumptions.** Resolution: completed
  in `9161fa1` (A2.1), `1e4c003` (A2.2), `893192a` (A2.3). Implementation: extracted a
  `_core` theorem carrying the existing body and retained each original public theorem as a
  one-line source-facing wrapper; **A2 exposed four body-unused hypotheses** (`0 ≤ D` and the
  Hilbert-log-diameter bound in `BirkhoffHopf.lean`; the box-bounds and `γ < 1` in
  `FranklinLorenz.lean`), all dropped from the cores. No public declaration deleted or
  renamed; no proof-body change beyond binder removal. Validation: `lake env lean` exit 0 per
  file; full build 8761 jobs exit 0; five named axiom reports clean.
- **P1 / Overlay A3 — ProjectiveLag dependency truthfulness.** Resolution: completed in
  `8356468`. Implementation: body-only rewire of the production drift-envelope wrapper to the
  direct Franklin--Lorenz convergence theorem. Deviation: none — **the alternate compactness
  seam was retained but removed from the production route** exactly as recommended; docstrings
  corrected and the obsolete Carroll/Birkhoff--Hopf implemented-route reference removed.
  Validation: `lake env lean` exit 0; full build 8761 jobs exit 0; reference sweep confirms
  the reconstructed convergence theorem has no production client.
- **S1 / Overlay A4 — continuum honesty.** Resolution: completed in `d7866bb`. Implementation:
  **the two tautological `True`-valued scaffolds were deleted rather than replaced with
  premature interfaces** (S1.1 generation theorem — no clients; S1.2 uniform-integrability
  marker — fed an ignored `True`), and the ignored `(_hui : True)` binder (S1.3) was removed
  with its caller updated. Retained: the one-sided measurability bound, finite-dyadic AC
  theorem, explicit density-closure theorem, assembly wrappers. Future targets moved to
  roadmap prose on the canonical anchored-interval carrier. Validation: both files
  `lake env lean` exit 0; full build 8761 jobs exit 0.
- **D2 — proof pluralism as a feature.** Resolution: the two Birkhoff routes are documented as
  intentional independent developments in README/STATUS (direct = Doeblin/weighted-average;
  paper = Eveson--Nussbaum with the sharper coefficient); route-independence is re-swept each
  batch and now enforced textually by `check_documentation_consistency.py`.
- **D1 / D3 — status language and stale roadmap.** Resolution: the global-completion-slogan
  prohibition is preserved and enforced by `check_documentation_consistency.py`; stale
  A0/A2/A3/A4 "pending" lines removed from the live docs and remediation plan; the README
  matrix-scaling namespace error was corrected to `ForMathlib.matrix_scaling_exists`.
- **T1 — audit tooling prerequisites.** Resolution: completed in `c0c0495`. A missing `lake`
  executable in `check_comparator_signatures.py` now yields a concise prerequisite message and
  controlled exit code 3 instead of an unhandled `FileNotFoundError`; a new
  `check_nonvacuous_scaffolds.py` ratchet guards against reintroducing `True`-shaped scaffolds.
- **P3 — internal Birkhoff-route refactors:** not in this batch; no change. The two routes
  remain independent; internal restructuring is optional future API cleanup.
- **S2 / Overlay A5 — verification-data interfaces:** **explicitly deferred** until a real
  client consumes such an interface.
- **M1 (ENNReal Wasserstein), M2 (continuum path-space closure), M3 (worst-case optimizer
  attainment):** longer-horizon research overlays, out of scope for this remediation batch.

## D1. Replace completion slogans with scoped evidence

> **Resolution:** the slogan prohibition is preserved and now enforced by
> `scripts/check_documentation_consistency.py`; see the Resolution status section above.

**Class:** H / repository-wide documentation
**Risk:** low
**Card impact:** none
**Upstream value:** trust and reviewability

### Problem

Current documentation repeatedly summarizes repository or external-source quality using an absence-based slogan. This is both aggrandizing and ambiguous about scope. Some current files also mix production libraries, Challenge specifications, external repositories, and historical states in the same claim.

The audit helper reports the current occurrences in:

- `STATUS.md`;
- `PROOF_PIPELINE.md`;
- `FOUNDATIONS.md`;
- `SURVEY_LEADS.md`;
- `Challenge/README.md`;
- `formalization.yaml`;
- historical entries in `JOURNAL.md`.

### Preserve

- exact build observations;
- axiom reports;
- dates and commits;
- challenge intent;
- historical chronology.

### Step-by-step correction

1. Run:

   ```bash
   python3 scripts/audit_proof_shape.py --status-language
   ```

2. In current-status documents, replace slogans with command/result prose. Example:

   ```text
   At commit d814680..., `lake build` completed successfully in the maintainer's environment.
   The source scan over production libraries returned no admitted tactic tokens; Challenge
   conformance specifications are intentionally excluded. The named capstones reported only
   `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`.
   ```

3. In `formalization.yaml`, report separate fields or sentences for:

   - build result;
   - warning count;
   - production-source scan scope;
   - Challenge status;
   - axiom output;
   - comparator status.

4. In `JOURNAL.md`, preserve dates but normalize the wording. Historical entries should say what command was run and on which source state. Do not silently turn old observations into current guarantees.

5. In external-source surveys, replace broad quality labels with concrete observations such as:

   ```text
   The checked revision contains no admitted tactic tokens in its built library and uses an
   Apache-2.0 license; this audit did not independently rerun its full CI.
   ```

6. Re-run the helper and manually inspect all remaining hits. The helper's own regex implementation is excluded from the report.

### Acceptance criteria

- No current document uses the banned completion rhetoric.
- Challenge admissions are described as intentional conformance specifications.
- Every strong status statement includes scope and evidence.
- No theorem statement or proof changes in this overlay.

---

## D2. Document proof pluralism as a repository feature

> **Resolution:** documented as an intentional feature in README/STATUS and enforced by the doc-consistency ratchet; see the Resolution status section above.

**Class:** R / U
**Risk:** low for docs; medium for later refactors
**Card impact:** indirect, through Sinkhorn convergence support
**Upstream value:** high

### The two routes

#### Direct AI-discovered route

Location:

```text
ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean
```

Public theorem:

```lean
ForMathlib.Matrix.positive_kernel_birkhoff_hopf_contraction
```

Core theorem:

```lean
finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound
```

Characteristic steps:

1. normalize weighted sums;
2. sum the pairwise weight bound over one index;
3. obtain pointwise Doeblin inequalities;
4. derive two linear inequalities for the normalized ratios;
5. combine them into a Möbius bound;
6. apply the scalar logarithmic estimate.

The current proof does not perform Carroll's finite-simplex-to-two-atom linear-programming reduction.

#### Published Eveson–Nussbaum route

Location:

```text
ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/*
```

Public theorem:

```lean
ForMathlib.Matrix.BirkhoffHopf.PaperRoute.positive_kernel_birkhoff_hopf_contraction_paper_route
```

Characteristic steps:

1. positive-cone Hilbert formulas;
2. convex/nonnegative hull diameter;
3. positive-matrix image diameter;
4. reduction to a two-dimensional subspace;
5. normalized `2 × 2` form;
6. scalar calculus bound;
7. sharp two-dimensional coefficient;
8. final finite-kernel assembly.

### Preserve

- both public theorems;
- the sharper paper-route result and its source mapping;
- the direct route's independent hard argument;
- route-specific files and theorem names;
- the fact that downstream Franklin–Lorenz needs only one public coefficient seam.

### Documentation edits

1. Add a short feature section to `README.md` after the library map or status pointer:

   ```text
   ## Two independent Birkhoff–Hopf proofs

   The finite positive-kernel contraction theorem is formalized twice intentionally.
   `BirkhoffHopf.lean` contains a short AI-discovered Doeblin/weighted-average proof.
   `BirkhoffHopf/PaperRoute/*` follows the Eveson–Nussbaum proof architecture and
   retains the sharper two-dimensional constant. Their coexistence is part of the
   research value of the repository: it permits comparison of a machine-discovered
   proof with a source-faithful formalization of published human reasoning.
   ```

2. Keep the strong existing comparison table in `STATUS.md`, but update its heading and surrounding language to avoid triumphalist status claims. State the theorem names and proof dependencies instead.

3. Rewrite the stale projective section at the start of `PROOF_PIPELINE.md`. It still describes open goals and says to sequester a route that is now complete. Preserve it only as a dated history subsection or replace it with a current comparison and maintenance policy.

4. Expand the module header of `BirkhoffHopf.lean` to identify the direct proof as independently discovered and to summarize the Doeblin argument.

5. Keep the `PaperRoute/Assemble.lean` header explicit that it is source-faithful and independent of the direct contraction proof.

6. Add a maintenance note:

   ```text
   Refactors may share definitions and elementary Hilbert-metric lemmas, but must not
   make either route invoke the other route's contraction theorem or route-specific hard core.
   ```

### Independence checks

After any Birkhoff refactor:

```bash
# The direct file should not import PaperRoute.
rg -n '^import .*PaperRoute' ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean

# The paper route should not close its hard step by invoking the direct public theorem.
rg -n 'exact .*positive_kernel_birkhoff_hopf_contraction|apply .*positive_kernel_birkhoff_hopf_contraction' \
  ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute

lake env lean ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf.lean
lake env lean ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/Assemble.lean
lake build ForMathlib
```

The second grep is heuristic; comments and qualified names must be inspected manually.

### Acceptance criteria

- README identifies the two proofs as intentional and worthy of study.
- The direct route is not mislabeled as Carroll's implemented LP reduction.
- The paper route retains source theorem references and the sharp constant.
- Neither proof route depends on the other's route-specific hard theorem.

---

## S1. Preserve continuum scaffolding while removing vacuous theorem encodings

> **Resolution:** completed in `d7866bb` — the two `True`-valued scaffolds were deleted (not replaced with premature interfaces) and the ignored `True` binder removed; see the Resolution status section above.

**Class:** S
**Risk:** medium
**Card impact:** none for the current card inequalities; relevant to the stronger continuum program
**Upstream value:** medium to high

### Important preservation fact

The repository already contains a substantially better canonical scaffold in:

```text
ChenGeorgiouPavon2021/Continuum/PathSpace.lean
ChenGeorgiouPavon2021/Continuum/IntervalPath.lean
ChenGeorgiouPavon2021/Continuum/IntervalWiener.lean
```

In particular:

- `ContinuousAnchoredIntervalPath` is the intended narrow carrier;
- `HasBoundedIntervalDyadicGridDensity` records the density seam;
- `HasContinuousAnchoredIntervalDyadicGeneration` records the measurable-generation seam;
- `HasIntervalDyadicKLExhaustion` records the KL-exhaustion seam;
- finite dyadic density and absolute-continuity results are genuine proof-bearing results.

Do not remove these modules while cleaning the older `RealPath := ℝ → ℝ` wrappers.

### S1.1 Obsolete `True` generation theorem

Current declaration:

```text
Continuum/KLExhaustion.lean:24
`dyadicNormalizedIncrementMap_generates_standardWienerRealPathMeasure`
```

It has no Lean clients. The desired statement is also false or at least overstrong on unrestricted `RealPath` without anchor and path-regularity constraints.

#### Safe correction

1. Confirm clients:

   ```bash
   rg -n '\bdyadicNormalizedIncrementMap_generates_standardWienerRealPathMeasure\b' --glob '*.lean' .
   ```

2. Keep the genuine one-sided theorem:

   ```lean
   dyadicNormalizedIncrementMap_iSup_comap_le_standardWienerRealPathMeasure
   ```

3. Remove the theorem proving `True`.

4. Replace its docstring with a module comment pointing to:

   ```lean
   HasContinuousAnchoredIntervalDyadicGeneration
   normalizedContinuousAnchoredIntervalDyadicIncrementMap_iSup_comap_eq
   ```

5. Add or update the roadmap entry saying that generation belongs on `ContinuousAnchoredIntervalPath`, not unrestricted `RealPath`.

6. Do not create a new theorem claiming the old name. If a named target is useful, use an unproved proposition definition:

   ```lean
   def ContinuousAnchoredIntervalDyadicGenerationTarget : Prop :=
     (inferInstance : MeasurableSpace ContinuousAnchoredIntervalPath) ≤
       ⨆ level, MeasurableSpace.comap
         (normalizedContinuousAnchoredIntervalDyadicIncrementMap level) inferInstance
   ```

   Prefer the existing structure if it already expresses the target sufficiently.

### S1.2 Uniform-integrability marker

Current declaration:

```text
Continuum/QuasiInvariance.lean:66
`cameronMartinDyadicDensity_uniformIntegrability_of_isCameronMartinPath`
```

It proves `True` and is used only to feed an ignored `_hui : True` argument into an absolute-continuity wrapper.

#### Safe correction

1. Preserve these genuine results:

   ```lean
   finiteDyadic_withDensity_standardWienerRealPath_shift_of_isCameronMartinPath
   finiteDyadic_absCont_standardWienerRealPath_shift_of_isCameronMartinPath
   ForMathlib.MeasureTheory.absolutelyContinuous_of_densityProcess
   ForMathlib.MeasureTheory.uniformIntegrable_one_of_lintegral_sq_bdd
   ```

2. Remove `_hui : True` from `absCont_of_finiteDyadic_absCont_and_density_closure`.

3. Remove the theorem proving `True` after the client is migrated.

4. Rename the remaining adapter so it states what it actually consumes. For example:

   ```lean
   theorem pathShift_absCont_of_supplied_absCont
       ...
       (hac : shiftedMeasure ≪ baseMeasure) :
       shiftedMeasure ≪ baseMeasure := hac
   ```

   Better still, let final assembly accept `hac` directly and remove the identity adapter after confirming no external clients.

5. Preserve the future target in `PLAN_CONTINUUM_CLOSURE.md` with the exact intended mathematical ingredients:

   - a filtration on the canonical path carrier;
   - local density process;
   - martingale consistency;
   - an `L²` bound or another uniform-integrability criterion;
   - application of `absolutelyContinuous_of_densityProcess`.

6. When the actual theorem is attempted, its conclusion must be a concrete `UniformIntegrable ...` proposition or an absolute-continuity result derived from one. Do not reintroduce a marker theorem with a proposition unrelated to the intended content.

### S1.3 Identity wrappers around interfaces

Examples:

```text
Continuum/KLExhaustion.lean:79
`hasDyadicKLExhaustion_standardWienerRealPathMeasure`

Continuum/QuasiInvariance.lean:80
`cameronMartinDyadicDensity_closes_path_absCont_of_isCameronMartinPath`
```

These may be useful as migration adapters, but their names imply derivation from Wiener or Cameron–Martin hypotheses when their proofs simply return supplied interface data.

#### Two-overlay migration pattern

**Overlay 1:** add truthful names and migrate clients.

```lean
theorem hasDyadicKLExhaustion_of_interface
    (W : ProbabilityMeasure RealPath)
    (hKL : HasDyadicKLExhaustion W) :
    HasDyadicKLExhaustion W := hKL
```

For absolute continuity, final assembly can usually consume `hac` directly; an identity theorem is unnecessary unless it stabilizes an API.

**Overlay 2:** after repository-wide search, remove or retain the old names as explicitly documented compatibility adapters.

Do not remove `HasDyadicKLExhaustion`, `HasIntervalDyadicKLExhaustion`, or the canonical interval-carrier target structures.

### Expected friction

- Changing a wrapper's argument list can cascade through `Continuum/Assembly.lean` and `IntervalWiener.lean`.
- Aggregate module checks require imported `.olean` files; use `lake build ChenGeorgiouPavon2021` before direct checking of aggregate files.
- The unrestricted `RealPath` and canonical `IntervalPath` layers have similar names; verify the carrier on every theorem before editing.

### Acceptance criteria

- No theorem in the continuum target layer concludes merely `True`.
- Finite dyadic density results remain intact.
- Canonical anchored-continuous path scaffolding remains intact.
- Missing continuum mathematics is represented by named interfaces or proposition definitions.
- Final assembly theorem names do not imply that an assumption was derived when it was merely supplied.

---

## S2. Preserve PDE/SDE targets while separating verification data from analytic derivation

> **Resolution:** explicitly deferred (Overlay A5) until a real client consumes a verification-data interface; no change in this batch.

**Class:** S / U
**Risk:** medium
**Card impact:** low for current abstract card capstones; high for a concrete CGP model
**Upstream value:** medium

### Problem

The primitive theorem in `SocOt/DynamicTargets.lean` is appropriately minimal:

```lean
isOptimalSOC_of_feasible_and_energy_le
```

The Hopf–Cole and Hamilton–Jacobi wrappers retain PDE hypotheses but do not use them. They use separately supplied endpoint feasibility and global variational optimality, which already imply the conclusion.

The target concept is valuable. The current theorem names merely blur the distinction between:

- deriving verification conditions from PDE/SDE hypotheses;
- assembling optimality from already supplied verification conditions.

### Preserve

- `SchrodingerSystem` and `HamiltonJacobi` target definitions;
- the minimal optimization theorem;
- a named future target connecting PDE/SDE hypotheses to verification data;
- source theorem numbers and CGP terminology.

### Step-by-step correction

1. Introduce a generic verification structure near the minimal theorem:

   ```lean
   structure SOCVerificationData
       (d : SBData X) (u : Control X)
       (ρ₀ ρ₁ : ProbabilityMeasure X) : Prop where
     feasible : Feasible d u ρ₀ ρ₁
     energy_le : ∀ v, Feasible d v ρ₀ ρ₁ →
       energy u (d.pathLaw u ρ₀) ≤ energy v (d.pathLaw v ρ₀)
   ```

2. Add:

   ```lean
   theorem isOptimalSOC_of_verificationData
       (h : SOCVerificationData d u ρ₀ ρ₁) :
       IsOptimalSOC d u ρ₀ ρ₁ :=
     isOptimalSOC_of_feasible_and_energy_le d u ρ₀ ρ₁ h.feasible h.energy_le
   ```

3. Rename or add assembly wrappers:

   ```lean
   hopfCole_control_isOptimalSOC_of_verificationData
   sigmaHopfCole_control_isOptimalSOC_of_verificationData
   valueGradient_control_isOptimalSOC_of_verificationData
   ```

4. Represent the unproved analytic goal as a proposition definition, not as a theorem:

   ```lean
   def HopfColeVerificationTarget (...) : Prop :=
     SOCVerificationData d feedbackControl ρ₀ ρ₁
   ```

   A later theorem should derive this target from a sufficiently concrete diffusion/PDE model.

5. Keep existing source-facing theorem names temporarily as wrappers if downstream code or prose references them, but rewrite their docstrings to say “assembly from verification data.” Do not claim the Schrödinger system alone implies the result in the current abstract `SBData` model.

6. Migrate `ProjectTheoremTargets.lean` comments. It still speaks of executable placeholders and a global progress bar, although the current target modules are interface-driven.

### Expected friction

- `omit [NormedSpace ℝ X]` blocks may need to move with the new structure/theorems.
- Universe and implicit-argument inference can become difficult if `d`, `u`, `ρ₀`, and `ρ₁` are fields rather than explicit parameters. Start with explicit parameters and only generalize after the file builds.
- Do not attempt the actual HJB/SDE verification theorem in the same overlay as this API cleanup.

### Acceptance criteria

- Assembly theorem names mention verification data or supplied conditions.
- PDE/SDE hypotheses appear only in propositions/theorems that use them.
- The future analytic target remains represented and searchable.
- `isOptimalSOC_of_feasible_and_energy_le` remains the small reusable optimization theorem.

---

## P1. Make the ProjectiveLag dependency graph truthful without discarding alternate-route scaffolding

> **Resolution:** completed in `8356468` — production wrapper rewired to the direct Franklin--Lorenz theorem, alternate seam retained; see the Resolution status section above.

**Class:** C / R
**Risk:** medium
**Card impact:** indirect through finite Sinkhorn convergence
**Upstream value:** medium

### Current dependency loop

In `Compactness/ProjectiveLag.lean`:

1. `sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_franklin_lorenz`
   proves convergence (`:1299`).
2. `no_positive_subsequence_of_pair_tendsto_zero` derives absence of a bad subsequence (`:1353`).
3. `...no_positive_subsequence_from_gauge_iterates` applies step 2 to step 1 (`:1391`).
4. `...tendsto_zero_from_gauge_iterates` derives convergence again from step 3 (`:1428`).

The current comments at `:1383-1390` call step 3 the hard theorem and describe an independent compactness contradiction proof, but the implemented proof is a corollary of step 1.

### Preserve

- the Franklin–Lorenz production proof;
- the general no-positive-subsequence criterion if it is useful;
- the Sinkhorn-specific no-subsequence statement as a possible seam for a future independent proof;
- public theorem names used downstream.

### Lowest-risk correction: documentation first

1. Change the docstring of the Sinkhorn-specific no-subsequence theorem to:

   ```text
   Derived no-positive-subsequence corollary of the Franklin–Lorenz convergence theorem.
   Retained as an interface for a possible independent compactness/cluster-point proof.
   The present implementation is not independent.
   ```

2. Change the final convergence theorem's docstring so it does not claim that the no-subsequence theorem is the Sinkhorn-specific hard core.

3. Build only this file and its aggregate before any dependency rewrite.

### Preferred dependency cleanup

In a second overlay:

1. Keep the public final theorem name:

   ```lean
   sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_gauge_iterates
   ```

2. Prove it directly by applying:

   ```lean
   sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_franklin_lorenz
   ```

3. Retain:

   ```lean
   no_positive_subsequence_of_pair_tendsto_zero
   sinkhorn_backward_denominator_projective_ratio_spreads_no_positive_subsequence_from_gauge_iterates
   ```

   as derived corollaries in a clearly labeled subsection such as “Consequences and alternate compactness seam.”

4. If a future agent proves the no-subsequence theorem independently from compactness, replace only its body and update the docstring. The production theorem can remain on the direct Franklin–Lorenz path until the independent proof is reviewed.

5. Do not delete the generic converse criterion `tendsto_pair_nonnegative_atTop_zero_of_no_positive_subsequence` merely because it leaves the production dependency path. It encodes a legitimate topology lemma and may support the alternate proof.

### Optional later file split

Only after the dependency correction is stable, move the generic topology lemmas and alternate seam to a small file such as:

```text
Compactness/NoPositiveSubsequence.lean
```

Keep `ProjectiveLag.lean` as the public assembly import.

### Verification

```bash
rg -n 'sinkhorn_backward_denominator_projective_ratio_spreads_tendsto_zero_from_gauge_iterates' \
  --glob '*.lean' .

lake env lean ChenGeorgiouPavon2021/SocOt/Sinkhorn/Convergence/Compactness/ProjectiveLag.lean
lake build ChenGeorgiouPavon2021
lake build
```

### Acceptance criteria

- The production convergence theorem has a direct, readable dependency on Franklin–Lorenz.
- The no-subsequence theorem remains available and is accurately labeled as derived unless independently reproved.
- No alternate-route scaffold is deleted solely because it has no current production client.

---

## P2. Decompose `matrix_scaling_exists` conservatively

> **Resolution:** completed in `3791d88`/`1c9054b`/`3ba1d17`/`36265ff` — a 47-line assembly over eight private lemmas, public statement unchanged; see the Resolution status section above.

**Class:** U
**Risk:** high
**Card impact:** indirect; finite Schrödinger-potential existence
**Upstream value:** very high

### Current state

`ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean:49-354` is a 318-line proof. It is mathematically valuable and a plausible upstream contribution. Its current monolithic form makes maintenance and review difficult, but an aggressive refactor is likely to trigger elaboration friction because many local definitions and positivity facts are tightly coupled.

### Preserve

- theorem statement of `matrix_scaling_exists`;
- log-domain convex-minimization proof strategy;
- mass-conservation hypothesis and its explanatory comments;
- empty-index branch;
- downstream theorem `sinkhorn_potentials_exist`.

### Do not start with a file split

First extract lemmas inside the same file. A file split changes namespaces/imports and makes errors harder to localize.

### Extraction order for a weaker agent

#### Stage 1: extract the final algebraic assembly

The lowest-risk region is `:312-354`, after the minimizer and stationarity relation already exist.

1. Extract the “mass conservation kills the common multiplier” calculation into a private lemma.
2. Give the lemma only algebraic inputs:

   - positivity/nonzeroness of `b`;
   - `∑ b = 1`;
   - row equations defining `a`;
   - common-stationarity relation;
   - equality of total masses.

3. Avoid passing local abbreviations `P`, `Q`, `D2`, and `μ` when their definitions can be unfolded at the call site. If the signature becomes unreadable, introduce a small private structure for the algebraic stationarity data.

4. Build after this extraction before touching calculus.

Suggested name:

```lean
private theorem sinkhorn_stationarity_constant_eq_zero
```

#### Stage 2: extract the directional derivative result

Region `:211-311` proves that a stationarity expression is independent of the coordinate.

1. Keep the line-restriction `Fc` and direction `w = e_j - e_j0` inside one lemma.
2. Pass the established minimizer facts:

   - `IsMinOn ψ K bs`;
   - strict interior lower bound for `bs`;
   - simplex sum;
   - positivity of kernel row sums.

3. Return only the coordinate-independence equation, not all derivative intermediates.

Suggested name:

```lean
private theorem sinkhorn_stationarity_difference_eq_base
```

4. Scope any increased heartbeat setting around this lemma first. Do not leave a module-wide setting unless another extracted lemma still requires it.

#### Stage 3: extract compact truncation and minimizer existence

Regions `:82-201` contain:

- kernel-sum lower bound;
- objective lower bound;
- coordinate lower bound for a sublevel set;
- compact truncated simplex;
- existence of a minimizer.

Do not split each three-line fact into a separate public theorem. Extract a coherent result returning:

```text
δ > 0,
bs in the truncated simplex,
bs minimizes ψ on that simplex,
ψ bs ≤ ψ u,
and every coordinate of bs is strictly positive.
```

Suggested private structure:

```lean
private structure SinkhornSimplexMinimizerData ... where
  delta : ℝ
  delta_pos : 0 < delta
  b : ι → ℝ
  b_sum : ∑ j, b j = 1
  b_lower : ∀ j, delta ≤ b j
  isMinOn : IsMinOn ψ K b
  objective_le_uniform : ψ b ≤ ψ u
```

Use a structure only if it materially shortens later signatures.

#### Stage 4: shorten the public theorem

The final public theorem should read as a mathematical assembly:

1. handle empty index type;
2. obtain minimizer data;
3. define row scaling;
4. obtain stationarity relation;
5. prove multiplier vanishes;
6. assemble row and column equations.

### Expected friction and remedies

- **Local definitions do not elaborate outside the theorem.** Move definitions such as the objective `ψ` to a private `noncomputable def` only if necessary. Otherwise parameterize the extracted lemma by the function itself.
- **`classical` inference failures.** Add `classical` at the start of each private lemma rather than globally widening assumptions.
- **Derivative expressions become syntactically different.** Preserve the existing rewrite order and use a final `simpa` at the call site instead of normalizing all expressions in the helper theorem.
- **Heartbeat regression.** Narrow the setting with:

  ```lean
  set_option maxHeartbeats 1000000 in
  private theorem ... := by
    ...
  ```

- **Upstream API pollution.** Keep implementation lemmas private until their independent reuse is demonstrated.

### Verification

```bash
lake env lean ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean
lake build ForMathlib
lake env lean ChenGeorgiouPavon2021/SocOt/Sinkhorn/FiniteSystem.lean
lake build
```

Also check the public statements have not changed with `#check` or the comparator signature tool.

### Acceptance criteria

- `matrix_scaling_exists` statement unchanged.
- Proof body becomes a short assembly of named stages.
- Heartbeat override is scoped as narrowly as practical.
- No change to the mathematical proof route.
- Helper theorems remain private unless deliberately prepared for upstream review.

---

## P3. Refactor each Birkhoff route internally without merging them

> **Resolution:** not in this batch; the two routes remain independent. Optional future API cleanup.

**Class:** R / U
**Risk:** medium to high
**Card impact:** indirect through Franklin–Lorenz
**Upstream value:** high

### P3.1 Direct route

The 144-line theorem at `BirkhoffHopf.lean:462` already contains a good six-step narrative. Extract route-specific lemmas matching that narrative.

Suggested decomposition:

1. `pairwise_weight_bound_implies_doeblin_left`
2. `pairwise_weight_bound_implies_doeblin_right`
3. `doeblin_bounds_imply_first_linear_ratio_bound`
4. `doeblin_bounds_imply_second_linear_ratio_bound`
5. `two_linear_ratio_bounds_imply_mobius_bound`
6. existing `log_mobius_le_one_sub_mul_log`

The public finite-weighted-average theorem then normalizes sums, invokes these lemmas, and applies the scalar log bound.

#### Preserve route identity

- Do not use `PaperRoute.TwoByTwo` to prove the direct theorem.
- Do not reintroduce Carroll's LP reduction merely to match the literature; the direct proof's novelty is that it avoids it.
- Keep the two-point theorem as a corollary of the finite theorem in this route.

### P3.2 Paper route

`PaperRoute/Assemble.lean:51` is a 237-line source-faithful assembly. Its length is less concerning because the route intentionally mirrors a published chain. Refactor only where theorem names improve source correspondence.

Suggested internal seams:

1. decomposition of source vectors into two nonnegative image-cone generators;
2. image-cone diameter bound for those generators;
3. pairwise cross-ratio conversion;
4. construction of the `2 × 2` matrix for an output pair;
5. evaluation/cancellation of the `2 × 2` images;
6. final spread assembly.

Keep source citation references on the theorem that corresponds to each paper step.

### Shared code policy

Safe to share:

- definitions of Hilbert spread and positive-kernel application;
- positivity lemmas;
- elementary `sSup` packaging;
- coordinate scaling/permutation invariance.

Do not share between routes:

- the direct Doeblin reduction;
- the paper's two-dimensional subspace reduction;
- the route-specific scalar contraction theorem;
- the final route-specific contraction assembly.

### Acceptance criteria

- Both route public theorems remain independently checkable.
- Direct route proof is shorter and exposes reusable elementary inequalities.
- Paper route remains traceable to cited propositions and lemmas.
- No “deduplication” removes the comparative research value.

---

## A1. Minimize reusable theorem assumptions while preserving paper-facing wrappers

> **Resolution:** completed in `9161fa1`/`1e4c003`/`893192a` (Overlay A2) — `_core` lemmas + retained wrappers, four body-unused hypotheses dropped; see the Resolution status section above.

**Class:** U / H
**Risk:** medium
**Card impact:** low to medium
**Upstream value:** high

### General recipe

For each theorem with an unused hypothesis:

1. determine whether the hypothesis is mathematically implied, presentation-only, or genuinely accidental;
2. add a minimal `_core` theorem;
3. keep the old theorem as a wrapper if it corresponds to a source statement or stabilizes downstream code;
4. migrate paper-agnostic clients to `_core`;
5. only remove the wrapper if it has no source-fidelity or compatibility value.

### Candidate A1.1 — Franklin–Lorenz geometric bound

`Compactness/FranklinLorenz.lean:184`

The box-bound and strict-contraction assumptions should be separated by role:

- the pointwise geometric inequality needs the contraction property and nonnegativity of the coefficient;
- strict `γ < 1` is needed for convergence of the geometric envelope;
- box bounds may belong to a Sinkhorn-facing wrapper rather than the projective core.

#### Prescription

1. Add a core theorem containing only assumptions referenced by the proof.
2. Retain the existing theorem name as a wrapper if it matches Franklin–Lorenz/Sinkhorn context.
3. Move `γ < 1` to the first theorem that proves `Tendsto` of `γ ^ k`.
4. Do not remove gauge or box assumptions from higher-level paper wrappers solely because a lower-level inequality does not use them.

### Candidate A1.2 — general weighted-average Birkhoff theorem

`BirkhoffHopf.lean:462`

The abstract theorem receives `0 ≤ D`, but its pairwise hypotheses on all ordered pairs may already imply the needed diagonal nonnegativity when the index type is nonempty.

#### Prescription

1. Prove a small lemma deriving `0 ≤ D` from a diagonal instance if that implication is robust.
2. Add a core theorem without `hD`.
3. Keep the two-point wrapper's explicit `hD` if it is convenient for synthesizing diagonal cases.
4. Avoid making the direct proof harder merely to remove one assumption; statement cleanliness is secondary to route clarity.

### Candidate A1.3 — pointwise matrix theorem with unused diameter hypothesis

`BirkhoffHopf.lean:687`

The proof uses the explicit cross-ratio bound, not the supplied image-diameter assumption.

#### Prescription

1. Add a theorem named from the assumptions actually used, for example:

   ```lean
   positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction
   ```

2. Make the current diameter-oriented theorem a wrapper if its name is useful in the paper/API chain.
3. Do not pass an unused diameter object through the direct route merely to imitate the paper route.

### Candidate A1.4 — source-paper DRO wrappers

Large source-facing theorems in `GaoKleywegt2023/Basic.lean` and `MohajerinEsfahaniKuhn2018/Basic.lean` contain assumptions that may be unused after stronger shared infrastructure was added.

#### Prescription

- Preserve theorem-number-faithful wrappers.
- Move the minimal mathematical result into `ForMathlib.OptimalTransport` when it is paper-agnostic.
- Make the paper theorem a short specialization with source notation.
- Do not rewrite all source-facing APIs in one patch; they are literature-facing surfaces with distinct fidelity constraints even though they do not gate the card inequalities.

### Acceptance criteria

- Minimal reusable theorems expose only mathematical dependencies.
- Source-faithful wrappers remain available where useful.
- No theorem statement is weakened or strengthened accidentally.
- Client migration is explicit and verified.

---

## D3. Correct stale status and roadmap contradictions

> **Resolution:** completed across the A0/A6 docs sweep — stale pending lines removed, namespace error fixed, ratchets added; see the Resolution status section above.

**Class:** H
**Risk:** low
**Card impact:** none
**Upstream value:** reviewer orientation

### Current contradictions

- `README.md` still describes Sinkhorn convergence as the live frontier, while the current status records the finite Birkhoff–Hopf and Sinkhorn convergence developments as present.
- The start of `PROOF_PIPELINE.md` describes open projective goals and route selection that have since been resolved.
- `ProjectTheoremTargets.lean` says executable placeholders are intended as a progress bar, but the current modules use hypothesis/structure interfaces.
- `ForMathlib.lean` still labels several completed modules as staging placeholders.
- `STATUS.md` contains different descriptions of whether strong duality still carries a gap hypothesis; distinguish the lower-level theorem with an explicit `hge` parameter from the regularity/Slater capstones that discharge it.

### Step-by-step correction

1. Treat executable declarations as authoritative.
2. For each status paragraph, cite the exact theorem name rather than a broad area label.
3. Distinguish:

   - theorem with an explicit interface argument;
   - theorem that derives the interface under regularity;
   - final card inequality.

4. Move superseded work-plan sections under a heading such as:

   ```text
   Historical plan — superseded on 2026-07-10
   ```

5. Update aggregate module docstrings after proof status changes; these are commonly read by agents and can perpetuate obsolete work.

### Acceptance criteria

- No file calls a completed finite theorem the current open frontier.
- Interface-bearing and interface-discharging theorem variants are clearly distinguished.
- Historical plans remain available but are visibly dated and superseded.

---

## T1. Improve repository audit tooling prerequisite errors

> **Resolution:** completed in `c0c0495` — missing `lake` now exits 3 with a concise message; see the Resolution status section above.

**Class:** tooling
**Risk:** low
**Card impact:** none

`scripts/check_comparator_signatures.py` raises a raw `FileNotFoundError` when `lake` is unavailable.

### Prescription

1. Resolve `lake` with `shutil.which("lake")`.
2. If absent, print:

   ```text
   error: `lake` was not found on PATH; install/activate the repository Lean toolchain before running comparator signature checks
   ```

3. Return a nonzero status without a Python traceback.
4. Preserve the existing command behavior when Lake is available.
5. Add a small unit-style invocation or shell check for the missing-prerequisite branch.

This is a separate small overlay and should not be mixed with proof refactors.

---

# Longer research campaigns

The following are not cleanup tasks for a weak agent. They require mathematical design and should begin only after the lower-risk documentation/interface work is stable.

## M1. Canonical ENNReal Wasserstein transport cost

**Class:** U / semantic strengthening
**Risk:** very high
**Card impact:** potentially high
**Upstream value:** very high

`ForMathlib/OptimalTransport/Basic.lean` defines the general transport cost and OT value in `ℝ` via Bochner integrals. The Sinkhorn objective already has an `ℝ≥0∞` foundation that represents nonintegrability as `⊤` rather than a junk real value.

### Required design phase

Before editing downstream proofs, write a design note specifying:

- nonnegative cost type (`α → β → ℝ≥0∞` or a real nonnegative cost coerced to ENNReal);
- canonical `couplingCostENN` and `otCostENN`;
- finiteness predicates;
- `.toReal` compatibility theorems;
- relation to existing squared-distance definitions;
- migration plan for weak/strong duality and card-facing balls.

### Staging order

1. add ENNReal definitions without removing real ones;
2. prove compatibility under integrability/finiteness;
3. port coupling existence and elementary inequalities;
4. add ENNReal Wasserstein ball;
5. migrate paper-agnostic duality;
6. migrate card wrappers last;
7. remove real canonical definitions only after all clients move.

Do not mix this campaign with documentation or proof-route cleanup.

## M2. Genuine continuum path-space closure

**Class:** S / new mathematics
**Risk:** very high
**Card impact:** outside the current abstract card theorem; relevant to a concrete diffusion instantiation
**Upstream value:** high

The correct direction is already visible in `Continuum/PathSpace.lean`:

1. use anchored continuous paths on `[0,1]`;
2. prove bounded dyadic vertices are dense;
3. prove normalized dyadic increments separate paths;
4. derive measurable generation for the standard-Borel path carrier;
5. instantiate KL exhaustion;
6. construct the Cameron–Martin density process;
7. establish martingale consistency and uniform integrability;
8. derive quasi-invariance;
9. assemble KL = Cameron–Martin energy;
10. connect the path shift to the controlled diffusion model.

The audit recommends continuing on the canonical interval carrier rather than strengthening unrestricted `RealPath` statements.

## M3. Worst-case optimizer attainment

**Class:** source theorem extension
**Risk:** high

Keep value-duality theorems separate from optimizer-structure/attainment theorems. A later campaign may require tightness, semicontinuity, Prokhorov compactness, and measurable-selection infrastructure. Finite/discrete instances are suitable first targets.

---

# Recommended overlay sequence

## Overlay A0 — documentation consistency

- record the card theorem mapping and the named dependency reports;
- correct the card dependency graph;
- distinguish one-sided card inequalities from equality and optimizer theorems;
- document the two Birkhoff routes as a protected comparative feature;
- mark historical surveys, journals, and roadmaps as dated rather than current status.

No Lean theorem changes.

## Overlay A1 — decompose `matrix_scaling_exists`

Keep its public statement unchanged initially. Extract named stages for compact-domain
construction, objective continuity/attainment, boundary exclusion, stationarity, multiplier
elimination, and final scaling assembly. Build the leaf after each extraction. This is the
highest immediate upstream-value proof refactor.

## Overlay A2 — minimize assumptions through `_core` theorems

Start with one family per overlay:

1. `hard_core_franklinLorenz_right_column_pairwise_log_correction_geometric_bound`;
2. `finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound`;
3. `positive_kernel_birkhoff_hopf_pointwise_log_crossratio_contraction_of_apply_hilbert_log_diameter_bound`.

Use mechanically reported unused hypotheses as evidence, but retain paper-facing wrappers when
the assumptions make the source correspondence clearer.

## Overlay A3 — ProjectiveLag dependency clarification

- make the production convergence theorem invoke the Franklin--Lorenz convergence theorem directly;
- retain the no-positive-subsequence result as a derived theorem or alternate compactness scaffold;
- remove comments that call the derived round trip the hard core;
- delete conversion machinery only after exact client analysis shows it has no independent role.

## Overlay A4 — minimal continuum honesty correction

- delete the two theorem-shaped `True` markers;
- remove the ignored `True` value threaded to the quasi-invariance client;
- record the intended targets and prerequisites in the continuum roadmap;
- do not create a detailed proposition on the acknowledged-provisional unrestricted path carrier.

## Overlay A5 — verification-data APIs when demanded by clients

Add structures such as `SOCVerificationData` only when an existing assembly theorem consumes
meaningful fields. Do not introduce interface types merely to make distant roadmap items executable.

## Later research overlays

- route-preserving internal decomposition of the direct and paper Birkhoff proofs;
- ENNReal transport-cost foundation;
- canonical interval-path/KL-exhaustion/Cameron--Martin closure;
- worst-case optimizer attainment and source-generalization work.

# Structural hotspots

Largest files at the audited commit:

| Lines | Declarations | File |
|---:|---:|---|
| 1847 | 68 | `.../Compactness/ProjectiveLag.lean` |
| 925 | 44 | `ForMathlib/.../BirkhoffHopf.lean` |
| 842 | 18 | `GaoKleywegt2023/Basic.lean` |
| 760 | 21 | `WangGaoXie2023/Basic.lean` |
| 738 | 25 | `.../Compactness/FranklinLorenz.lean` |
| 609 | 15 | `.../Compactness/ScaleLag.lean` |
| 510 | 15 | `Drsb/Basic.lean` |
| 498 | 15 | `BirkhoffHopf/PaperRoute/TwoByTwo.lean` |
| 497 | 13 | `Sinkhorn/Convergence/Bounds.lean` |
| 490 | 13 | `MohajerinEsfahaniKuhn2018/Basic.lean` |

Longest approximate declaration spans:

| Lines | Declaration |
|---:|---|
| 318 | `matrix_scaling_exists` |
| 237 | `positiveKernel_birkhoff_contraction_from_twoByTwo` |
| 157 | `dataDriven_worstCase_cor2ii` |
| 144 | `finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound` |
| 135 | `worstCase_structure_cor1` |
| 124 | `hard_core_franklinLorenz_right_column_pairwise_log_correction_geometric_bound` |
| 120 | `exists_coupling_sinkhorn_lagrangian_eq` |
| 118 | `finite_six_stream_box_precluster_subsequence` |
| 107 | `mixed_projective_cross_drift_zero_of_ratio_drift_and_bounds` |
| 107 | `hasSinkhornDisintegration_of_isSinkhornPlan` |

These spans are triage signals. In particular, the long paper-route theorem should not be judged by line count alone because its source-traceable structure is part of its value.

# Final priority order

1. **Documentation consistency:** scoped evidence, exact card dependency graph, literature mapping,
   and preservation of the two Birkhoff routes.
2. **Highest upstream payoff:** decompose `matrix_scaling_exists` without changing its public type.
3. **Statement quality:** add minimal core theorems and retain source-facing wrappers.
4. **Dependency truthfulness:** simplify the production ProjectiveLag path while preserving alternate
   compactness scaffolding.
5. **Minimal continuum honesty:** remove theorem-shaped `True` markers and use roadmaps until the
   carrier and target statements stabilize.
6. **Longer campaigns:** Birkhoff route decomposition, ENNReal OT, canonical path-space closure,
   and optimizer attainment.

The current card inequalities are already isolated from the long-horizon continuum and
source-faithful optimizer campaigns. Accordingly, the next substantial proof work should be
chosen for upstream mathematical value, not from a mistaken belief that those campaigns gate the
card. The repository's most distinctive comparative asset remains the pair of independent
Birkhoff--Hopf proofs: one discovered during AI-assisted formalization and one organized around
published human reasoning. Refactors should make that comparison easier to inspect, not optimize
it away.
