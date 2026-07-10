# STATUS.md — dated checked state

**Snapshot base:** commit `ece61a237bab50ff7eef0d2a94fef651b7b01504`
**Snapshot date:** 2026-07-10

This file records dated observations. Evergreen project rules live in [`AGENTS.md`](AGENTS.md),
current work ordering lives in [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md), and historical narrative
lives in [`JOURNAL.md`](JOURNAL.md).

## Evidence and scope

The following observations concern different scopes and should not be collapsed into one
completion label.

### Production source scan

On the snapshot source tree, this command returned no matches:

```bash
grep -rn --include='*.lean' \
  --exclude-dir=.lake --exclude-dir=.reference-clones \
  --exclude-dir=reference --exclude-dir=Challenge \
  -w sorry .
```

`Challenge/**/Conformance.lean` is intentionally outside that scope. A separate scan finds
18 admitted challenge specifications there; their project-backed proofs are represented by the
sibling `Leaderboard.lean` files.

### Build report

The maintainer reported that `lake build` completed successfully on the Lean source state at
commit `d81468009ef35024fd213686133f38b234ec9054`, with 8761 jobs and no warnings. No Lean file
changed between `d814680` and this snapshot commit `ece61a2`; the intervening commits added the
audit/helper and removed unrelated prose material.

This document does not turn that report into a repository-wide theorem claim. Re-run `lake build`
after applying any overlay.

**Post-batch re-verification (2026-07-10, A3–A6 remediation).** After the A3 ProjectiveLag
rewire (`8356468`) and the A4 continuum-scaffold deletions (`d7866bb`), `lake build` completed
with 8761 jobs, exit 0; the A6 tooling/docs commit (`c0c0495`) changed no Lean file. The five
named axiom reports below were re-run at this state and are unchanged.

### Named capstone dependency reports

The maintainer reported:

```text
#print axioms Drsb.wdrsb_cost_bound
-- [propext, Classical.choice, Quot.sound]

#print axioms Drsb.sdrsb_cost_bound
-- [propext, Classical.choice, Quot.sound]
```

These reports concern exactly the two named card theorems. They do not certify every declaration
in the repository or the intentional Challenge specifications.

### Comparator status

The local signature pre-flight has been exercised. The real landrun comparator has not yet been
reported as run for this challenge layer.

```bash
python3 scripts/check_comparator_signatures.py
bash scripts/run_challenge_comparator.sh
```

## Evaluation-card theorem map

| Evaluation card | Lean theorem | What it establishes |
|---|---|---|
| `wdrsb_cost_bound.yaml` | `Drsb.wdrsb_cost_bound` | a source inside the quadratic Wasserstein ambiguity ball has expected value at most the Wasserstein-DRO dual bound |
| `sdrsb_cost_bound.yaml` | `Drsb.sdrsb_cost_bound` | a source inside the Sinkhorn ambiguity ball has expected value at most the Sinkhorn-DRO log-partition bound |

The card theorems take `V : X -> R` abstractly. `Drsb/Basic.lean` imports the
Chen--Georgiou--Pavon library for provenance and surrounding results, but neither card proof uses
the continuum CGP energy-identity chain as a proof-term dependency.

The closest published backing is:

- Blanchet--Murthy and Gao--Kleywegt for the Wasserstein-DRO bound;
- Wang--Gao--Xie for the Sinkhorn-DRO log-partition bound;
- Chen--Georgiou--Pavon for the intended stochastic-control interpretation of `V`.

The card inequalities are specializations/weak-duality consequences. They are not verbatim
statements from a single DRSB paper.

## Strong duality and `hge`

The repository deliberately exposes more than one theorem layer.

- `Drsb.wdrsb_strong_duality` is a factored assembly theorem and still accepts
  `hge : dualValue <= primalValue` as an explicit input.
- `Drsb.wdrsb_strong_duality_of_regularity` discharges that input using
  `GaoKleywegt2023.dualValue_le_primalValue`, whose reusable core is
  `ForMathlib.OT.dualValue_le_droValue`.
- `Drsb.sdrsb_strong_duality` no longer accepts an `hge` parameter. Its hard direction is
  discharged internally under a Slater/interiority hypothesis.
- `Drsb.sdrsb_strong_duality_of_radius_gt_independent_cost` provides a concrete sufficient
  condition for that Slater hypothesis.
- Neither card inequality accepts `hge`.

Thus `hge` corresponds directly to the hard direction of published Wasserstein-DRO strong
duality; it is not an invented non-literature assumption. It remains in one compatibility/factoring
interface while a stronger wrapper proves it from explicit regularity assumptions.

## Parallel source-faithful developments

`MohajerinEsfahaniKuhn2018.worstCaseExpectation_eq_dual` and the Gao--Kleywegt worst-case
structure theorems are valuable paper-facing developments. They are not dependencies of
`Drsb.wdrsb_cost_bound` or `Drsb.sdrsb_cost_bound`.

Some of these source-facing theorems intentionally retain explicit ingredient hypotheses such as
an extremal program value, a structured transport budget, or an attainment inequality. The Lean
proofs construct the remaining objects from those inputs; the theorem names should not be read as
claims that every premise of the published result has already been derived from primitive
regularity assumptions.

## Two Birkhoff--Hopf proof routes

The positive-kernel contraction result is present through two independent proof routes:

1. `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/Direct.lean` — an AI-discovered
   Doeblin/weighted-average argument;
2. `ForMathlib/LinearAlgebra/Matrix/BirkhoffHopf/PaperRoute/*` — a source-faithful
   Eveson--Nussbaum route.

The two routes share the route-neutral `BirkhoffHopf/Basic.lean` layer; the root
`BirkhoffHopf.lean` is a compatibility umbrella re-exporting `Basic` + `Direct`, and the paper
route imports `Basic` alone (never `Direct`), so the route-specific hard arguments are structurally
independent at the module-import level.

**Coefficient distinction (do not overstate the paper route).** *Both* public capstones export the
**same** coarse coefficient `positiveKernelBirkhoffCoefficient G = (B-1)/B`. The paper route proves
a sharper *local* two-dimensional coefficient `(α-1)/(α+1)` internally, but its assembly relaxes back
to the coarse global `(B-1)/B` — it does **not** yet export a sharper global matrix coefficient. The
gap `(α-1)/(α+1) < (α²-1)/α²` is formalized in `BirkhoffHopf/Comparison.lean`. The direct
implementation is not Carroll's linear-programming reduction, although Carroll remains useful
comparison literature.

Finite Sinkhorn convergence and the Franklin--Lorenz geometric-decay route are already represented
in the source tree. They are not the current card bottleneck.

## Continuum and stochastic-control scope

The continuum modules contain a mixture of:

- proved finite/sequence-model results;
- assembly theorems consuming explicit interfaces;
- long-horizon targets for interval path spaces, dyadic generation, KL exhaustion,
  Cameron--Martin quasi-invariance, and SDE/Girsanov closure.

These modules support the secondary goal of formalizing useful published mathematics. They do not
currently supply the abstract `V` consumed by the card theorems.

When a future statement is not stable because the current path carrier is known to be provisional,
prefer a roadmap entry over a theorem-shaped marker with vacuous content. Keep Lean interfaces only
when a present client consumes them or the intended proposition is sufficiently settled.

## Current work ordering

1. **Upstream finite mathematics:** decompose `ForMathlib.matrix_scaling_exists` into named,
   reviewable stages without changing its public statement.
2. **Assumption minimization:** add minimal `_core` theorems and retain paper-facing wrappers for
   source comparison.
3. **ProjectiveLag clarification:** make the production convergence theorem call the established
   Franklin--Lorenz result directly while preserving no-subsequence machinery as an alternate-route
   scaffold when it has independent value.
4. **Documentation and continuum honesty:** remove theorem-shaped `True` markers and record unstable
   future targets in the appropriate roadmap.
5. **Long-horizon theory:** develop the interval-path/SDE foundations only after statement design and
   dependency choices are explicit.

See [`PROOF_PIPELINE.md`](PROOF_PIPELINE.md) for step-by-step acceptance criteria.
