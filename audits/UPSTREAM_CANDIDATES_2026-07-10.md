# Upstream candidate dossier — finite matrix scaling & Birkhoff–Hopf (2026-07-10)

This is a **technical preparation document**, not a claim that Mathlib will accept the code. It
records the current shapes, proof architectures, imports, axiom reports, and proposed PR
decompositions for two Mathlib-facing developments produced during the U1–U5 upstream-preparation
campaign. All theorem names below are the stable *repository* exports; proposed eventual Mathlib
names are marked as proposals only.

Axiom baseline for every theorem listed here: `[propext, Classical.choice, Quot.sound]` (the standard
Mathlib foundations).

---

## 1. Matrix scaling / Sinkhorn existence

File: `ForMathlib/LinearAlgebra/Matrix/SinkhornScaling.lean` (573 lines).

### 1.1 Exported theorems and signatures

**Square (unchanged statement, `κ := ι` specialization):**

```lean
theorem ForMathlib.matrix_scaling_exists {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hsum : ∑ i, p i = ∑ j, q j)
    (G : ι → ι → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∃ a b : ι → ℝ, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      (∀ i, a i * ∑ j, G i j * b j = p i) ∧
      (∀ j, b j * ∑ i, G i j * a i = q j)
```

**Rectangular (the natural home of the argument):**

```lean
theorem ForMathlib.matrix_scaling_exists_rectangular
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hsum : ∑ i, p i = ∑ j, q j)
    (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∃ a : ι → ℝ, ∃ b : κ → ℝ,
      (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      (∀ i, a i * ∑ j, G i j * b j = p i) ∧
      (∀ j, b j * ∑ i, G i j * a i = q j)
```

**Schrödinger potentials (square + rectangular):**

```lean
theorem ForMathlib.sinkhorn_potentials_exist {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hsum : ∑ i, p i = ∑ j, q j) (G : ι → ι → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∃ φ0 φhat0 φ1 φhat1 : ι → ℝ, … (8.4a–8.4d)

theorem ForMathlib.sinkhorn_potentials_exist_rectangular
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hsum : ∑ i, p i = ∑ j, q j) (G : ι → κ → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∃ φ0 φhat0 : ι → ℝ, ∃ φ1 φhat1 : κ → ℝ,
      … φ0 i = ∑ j, G i j * φ1 j … φhat1 j = ∑ i, G i j * φhat0 i
      … φ0 i * φhat0 i = p i … φ1 j * φhat1 j = q j
```

### 1.2 Public theorem line counts

| theorem | source lines | ≈ span |
|---|---|---|
| `matrix_scaling_exists_rectangular` | 441–491 | ~50 (the assembly) |
| `matrix_scaling_exists` (wrapper) | 493–500 | ~8 |
| `sinkhorn_potentials_exist_rectangular` | 516–550 | ~35 |
| `sinkhorn_potentials_exist` (wrapper) | 553–571 | ~19 |

The optimization proof is **not** duplicated between square and rectangular: the square theorem is a
one-line delegation to the rectangular one at `κ := ι` (plus the empty-index branch); the rectangular
theorem holds the single copy of the assembly.

### 1.3 Proof architecture (private lemmas M1–M4d)

Method: a **log-domain convex minimization** (no Brouwer, no Birkhoff contraction). The scalings are
read off the first-order conditions of `ψ(b) = ∑ᵢ pᵢ·log(∑ⱼ Gᵢⱼ bⱼ) − ∑ⱼ qⱼ·log(bⱼ)` minimized over
the (column-side) open probability simplex; mass conservation `∑ p = ∑ q` forces the Lagrange
multiplier to vanish.

| tag | lemma | role | rectangular? |
|---|---|---|---|
| M4a.1 | `lower_bound_le_weighted_sum` | pointwise bound survives normalized weighting | single-type (used at `κ`) |
| M4a.2 | `simplex_coord_le_one` | simplex coordinate ≤ 1 | single-type (used at `κ`) |
| M4b | `exp_neg_div_le_coord_of_weighted_log_sum_ge` | logarithmic boundary coercivity | single-type (column `κ`) |
| M4c | `exists_isMinOn_truncated_simplex` | EVT on truncated finite simplex | single-type (column `κ`) |
| M1 | `common_column_residual_eq_zero` | mass conservation ⇒ residual `μ = 0` | **row ι + column κ** |
| M2 | `column_scaling_of_zero_residual` | zero residual ⇒ column scaling eqn | **row ι + column κ** |
| M3a | `stationarity_pairwise_residual_eq` | first-order condition along `eⱼ − e_{j₀}` | **row ι + column κ** |
| M4d | `exists_sinkhorn_interior_minimizer` | strict interior minimizer exists | **row ι + column κ** |

**Which private lemmas required nontrivial rectangular changes:** M1, M2, M3a, M4d had genuine
two-type generalization (row `ι`, column `κ`, kernel `G : ι → κ → ℝ`). Even for these the *proofs*
transferred essentially verbatim — the only body edits were type ascriptions on `set` bindings
(`w : κ → ℝ`, `ψ : (κ → ℝ) → ℝ`, `u : κ → ℝ`, `N = card κ`, `gmin` over `ι × κ`); the sum-exchange
(`Finset.sum_comm`), directional-derivative, and barrier arguments needed no new mathematics.
M4a/M4b/M4c stayed single-type generic and are simply instantiated at `κ` — **no change**.

### 1.4 Private helper classification (U2.2)

Policy this batch: **all eight helpers remain `private`.** M1/M2/M3a/M4d are proof-specific to matrix
scaling. M4a/M4b/M4c are plausibly reusable (finite-simplex EVT plumbing, log-barrier coercivity) but
are kept private until their names, hypotheses, and module homes are decided independently of this
proof — promoting any of them should be a separate commit with a source-independent docstring.

### 1.5 Imports (U2)

Minimal domain-level set replacing `import Mathlib` (each verified individually necessary — dropping
any one fails elaboration):

```
Mathlib.Analysis.SpecialFunctions.Log.Deriv   -- Real.log/exp, HasDerivAt.log, ContinuousOn.log
Mathlib.Analysis.Calculus.LocalExtr.Basic     -- IsLocalMin.hasDerivAt_eq_zero
Mathlib.Topology.Order.Compact                -- IsCompact.exists_isMinOn
Mathlib.Topology.MetricSpace.Bounded          -- isCompact_of_isClosed_isBounded, closedBall
Mathlib.Analysis.Normed.Group.Constructions   -- pi_norm_le_iff_of_nonneg
Mathlib.Data.Finset.Max                       -- Finset.exists_min_image / _max_image
```

`#lint only unusedArguments docBlame unusedHavesSuffices`: 0 findings across the four public
declarations.

### 1.6 Likely Mathlib home and proposed name

- Module home: `Mathlib/LinearAlgebra/Matrix/SinkhornScaling.lean` (new file). Mathlib has the
  Birkhoff polytope / doubly-stochastic matrices but neither Perron–Frobenius-as-a-theorem nor
  Sinkhorn scaling (grep-verified).
- Proposed eventual Mathlib name: `Matrix.exists_diagonal_scaling_of_pos` (rectangular primary), with
  `Matrix.exists_diagonal_scaling_of_pos_of_square` or a `κ := ι` corollary for the square case. Keep
  `ForMathlib.matrix_scaling_exists_rectangular` as the stable repository export for now.

### 1.7 Known limitations

- Real-valued strictly positive kernel only (no ℝ≥0∞ / general ordered field).
- Existence only — **no** uniqueness-up-to-scale theorem.
- **No** algorithmic (Sinkhorn iteration) convergence theorem in this module.
- Finite index types (`Fintype ι`, `Fintype κ`).

### 1.8 Potential PR split

1. private finite-simplex EVT + log-barrier coercivity lemmas (M4a–M4c), if promoted, as standalone
   `Analysis`-level lemmas with source-independent names;
2. rectangular `matrix_scaling_exists_rectangular` + square corollary;
3. `sinkhorn_potentials_exist(_rectangular)` as the discrete-Schrödinger-system corollary.

---

## 2. Birkhoff–Hopf finite positive-kernel contraction

Module layout after U3:

```
              BirkhoffHopf/Basic.lean         (route-neutral vocabulary; imports only Mathlib)
             /                       \
  BirkhoffHopf/Direct.lean       BirkhoffHopf/PaperRoute/*   (imports Basic)
             \                       /
        BirkhoffHopf.lean (umbrella: Basic + Direct)   BirkhoffHopf/Comparison.lean (imports both routes)
```

### 2.1 Neutral shared module

`BirkhoffHopf/Basic.lean` (482 lines) — 33 route-neutral declarations: the projective-kernel defs
(`positiveKernelApply`, `finiteHilbertProjectiveLogSpread`, `positiveKernelCrossRatio`,
`positiveKernelCrossRatioBound`, `positiveKernelBirkhoffCoefficient`,
`PositiveKernelApplyHilbertLogDiameterBounded`, the contraction-coefficient predicates
`IsBirkhoffHopfContractionCoefficient` / `IsStrictBirkhoffHopfContractionCoefficient`) plus
positivity / bound / finite-`sSup` bookkeeping and the transpose-invariance lemmas
(`positiveKernelCrossRatioBound_transpose`, `positiveKernelBirkhoffCoefficient_transpose`). Imports
**neither** proof route.

### 2.2 Direct route

`BirkhoffHopf/Direct.lean` (527 lines) — 13 declarations of the AI-discovered Doeblin /
weighted-average proof; imports `Basic`.

- Capstone: `ForMathlib.Matrix.positive_kernel_birkhoff_hopf_contraction`
  (`IsBirkhoffHopfContractionCoefficient G (positiveKernelBirkhoffCoefficient G)`).
- Hard scalar lemma: `finite_weighted_average_log_crossratio_contraction_of_pairwise_log_bound_core`
  (the finite-simplex Doeblin estimate), resting on `log_mobius_le_one_sub_mul_log` (the scalar
  Möbius bound proved calculus-free via weighted AM–GM).

### 2.3 Paper route

`BirkhoffHopf/PaperRoute/*` — the source-faithful Eveson–Nussbaum development; imports **only**
`Basic` (via `PositiveConeHilbert.lean`).

- Capstone:
  `ForMathlib.Matrix.BirkhoffHopf.PaperRoute.positive_kernel_birkhoff_hopf_contraction_paper_route`
  (same statement/coefficient as the direct capstone).
- Hard two-dimensional lemma: `PaperRoute.symmetricTwoByTwoPhi_le` — for the symmetric kernel
  `[[α,1],[1,α]]`, `symmetricTwoByTwoPhi α t ≤ (α-1)/(α+1)`, the sharp normalized `2 × 2` ratio.

### 2.4 Import graph and proof-reference independence

- `Direct.lean` imports `Basic` only (no PaperRoute import).
- Every PaperRoute file's transitive import closure is `PaperRoute → …submodules… →
  PositiveConeHilbert → Basic → Mathlib`; it never imports `Direct` or the root umbrella.
- The only PaperRoute mention of a Direct declaration is a doc comment in `PaperRoute/Assemble.lean`;
  no compiled reference exists.
- External clients (`FranklinLorenz.lean`, `Challenge/.../Leaderboard.lean`) import the root umbrella
  and keep working unchanged (they consume Direct capstones `..._strict_birkhoff_contraction_coefficient`
  / `..._of_apply_hilbert_log_diameter_bound`).

### 2.5 Exact exported coefficient

Both capstones export the **same** coarse coefficient
`positiveKernelBirkhoffCoefficient G = (B-1)/B`, where `B = positiveKernelCrossRatioBound G` is the
deliberately coarse finite cross-ratio **sum** bound.

### 2.6 Local sharp coefficient and executable comparison (U4)

`BirkhoffHopf/Comparison.lean` (81 lines; imports both routes — the only module for which that is
intended):

```lean
theorem symmetricTwoByTwoCoefficient_lt_coarse {α : ℝ} (hα : 1 < α) :
    (α - 1) / (α + 1) < (α ^ 2 - 1) / α ^ 2
```

The RHS is exactly `(B-1)/B` at the two-by-two cross-ratio diameter `B = α²`. The gap after clearing
denominators is `(α²-1)(α+1) − (α-1)α² = (α-1)(2α+1) > 0`. Also: `symmetricTwoByTwoCoefficient_le_coarse`
(`≤` corollary), `symmetricTwoByTwoPhi_lt_coarse` (chains the paper sharp bound), and
`both_routes_export_same_coarse_coefficient` (a witness that both capstones certify the identical
coefficient — the paper route does **not** hand back a sharper global coefficient).

### 2.7 What remains before a sharp *global* paper-route theorem (recorded, NOT started)

1. replace the finite cross-ratio **sum** bound `positiveKernelCrossRatioBound` by a finite **maximum**;
2. identify the exact image-cone projective diameter;
3. propagate the square-root / `tanh` coefficient through the paper assembly (it currently relaxes the
   local `(α-1)/(α+1)` back to `(B-1)/B`);
4. compare the resulting sharp global coefficient with the direct coarse coefficient;
5. decide whether downstream Franklin–Lorenz proofs benefit from the sharper rate (they currently only
   need a strict `γ < 1`).

### 2.8 Proposed PR decomposition (one plausible sequence, not the only one)

1. finite projective metric + positive-kernel basic API (`Basic.lean` contents);
2. the direct weighted-average contraction proof (`Direct.lean`);
3. the source-faithful Eveson–Nussbaum route (`PaperRoute/*`);
4. optional sharp-coefficient follow-up (the §2.7 campaign) + `Comparison.lean`.

---

## 3. Cross-cutting status

- Ready for upstream review: rectangular matrix scaling (§1), the Birkhoff `Basic` API and the two
  independent contraction routes (§2.1–2.3), the coefficient comparison (§2.6).
- Useful finite-mathematics follow-ups: promotion of M4a–M4c (§1.4), uniqueness-up-to-scale and
  Sinkhorn-iteration convergence (§1.7), the sharp-global-coefficient campaign (§2.7).
- Deferred continuum research: unaffected by this batch (Kolmogorov extension / Itô–Girsanov / Kakutani
  gaps tracked elsewhere).
