/-
# ForMathlib — paper-agnostic staging library

Reusable results, restated in Mathlib idiom, that the DRSB paper libraries import.
These are potential upstream Mathlib contributions (some already have complete
proofs in `reference/WellKnown.lean`; they are re-stated here with placeholder while we
audit statements against the papers, per the first-pass "statements only" policy).

One file per proposed Mathlib destination area:
* `ForMathlib.MeasureTheory.MeasurableArgmax` — **measurable ε-argmax selectors**: over a countable
  index set (`Nat.find` on an enumeration), and over a separable domain with a continuous integrand
  (the supremum is already achieved to within `ε` on a countable dense subset). This is the
  Kuratowski–Ryll-Nardzewski *substitute* the Wasserstein-DRO `≥` direction needs, and it avoids KRN
  entirely.
* `ForMathlib.MeasureTheory.DonskerVaradhanDual` — the DV **dual** variational formula
  `KL(μ‖ν) = sup_f (∫f dμ − log ∫eᶠdν)` (sup over bounded measurable `f`, **not** attained), and
  its corollary: setwise lower semicontinuity of `klDiv`, i.e. `KL`-balls are setwise closed.
  Distinct from the Gibbs formula below, which sups over *measures* and *is* attained.
* `ForMathlib.MeasureTheory.DonskerVaradhan` — the DV inequality / Gibbs variational
  identity (root fact under the Sinkhorn-DRO dual).
* `ForMathlib.MeasureTheory.Normalization` — normalize a finite nonzero measure to a
  probability measure (the `(μ univ)⁻¹ • μ` construction).
* `ForMathlib.MeasureTheory.GaussianEntropy` — Cameron–Martin relative entropy of a
  finite-dimensional Gaussian shift (`KL(N(·+h) ‖ N) = ½‖h‖²`), vendored from
  `mrdouglasny/gibbs-variational` (Apache-2.0; see the file header + README), plus the
  Euler–Maruyama discrete energy identity built on it.
* `ForMathlib.OptimalTransport.Basic` — the shared OT / DRO vocabulary (couplings,
  transport cost, Wasserstein-2 and Sinkhorn ambiguity balls, KL, DRO worst-case). The Kantorovich
  layer (`couplings`, `couplingCost`, `couplingCostENN`, `otCost`, `prodMeasure`, and the Sinkhorn
  objective/discrepancy/ball) is stated between **two** measurable spaces under a cost
  `c : α → β → ℝ`, with no algebra or topology; only the quadratic `couplingCost2`/`W2sq`/
  `wassersteinBall` need a single normed group.
* `ForMathlib.OptimalTransport.Coupling` — coupling existence (product / diagonal plans),
  extraction of near-optimal plans from the `otCost` infimum, and "finite second moments
  ⟹ every coupling has integrable quadratic cost". These are what let the DRSB
  Wasserstein cost bound drop its OT-*attainment* hypothesis.
* `ForMathlib.OptimalTransport.Convexity` — **the set of couplings is convex**, and `expect` /
  `couplingCost` are affine on it: `a·π₁ + (1−a)·π₂` couples `a·μ₁ + (1−a)·μ₂` with the *same* `ν`.
* `ForMathlib.OptimalTransport.DroValueFunction` — **the DRO value function
  `h t = sup{𝔼_μ[f] : ∃π ∈ Π(μ,ν), 𝔼_π[c] ≤ t}` is concave and nondecreasing.** Ingredient (3) of
  the last open edge `hge`; the other two are `ConverseLagrangian` and `Analysis.Supergradient`.
* `ForMathlib.OptimalTransport.StrongDualityGe` — **`hge`, proved**: the duality gap of
  Wasserstein-DRO is zero. `dualValue_le_droValue` assembles the converse Lagrangian bound, the
  optimal multiplier, and concavity of the DRO value function. This is Blanchet–Murthy Thm 1 /
  Gao–Kleywegt Thm 1, the theorem the four strong-duality capstones had carried as a hypothesis.
* `ForMathlib.OptimalTransport.DroValue` — the DRO worst-case value `sSup`: a function bounded
  above has bounded-above expectations, so the `BddAbove` side condition of every strong-duality
  theorem is a consequence of its own `λ = 0` conjugate hypothesis, not an assumption.
* `ForMathlib.Analysis.Supergradient` — **supergradient existence for concave functions on `ℝ`**
  (Mathlib has `ConcaveOn` and slope lemmas but no sub/supergradient existence, grep-verified), and
  the **DRO optimal multiplier** `exists_nonneg_multiplier`: for a nondecreasing concave value
  function there is `λ* ≥ 0` with `h t + λ*(δ − t) ≤ h δ`. This is ingredient (2) of the last open
  edge `hge`.
* `ForMathlib.OptimalTransport.ConverseLagrangian` — the **converse** of that bound: the Lagrangian
  value `𝔼_ν[φ_λ]` is *achieved*, to within `ε`, by pushing the nominal forward along a measurable
  near-maximizer of the `c`-transform. Together with `WeakDuality` this pins the Lagrangian
  supremum exactly. It is ingredient (1) of the last open edge `hge`; ingredient (2) is the optimal
  multiplier / complementary slackness.
* `ForMathlib.OptimalTransport.WeakDuality` — the per-coupling Lagrangian bound (the
  always-true `≤` half of OT-DRO duality). STAGING (placeholder); see `FOUNDATIONS.md`.
* `ForMathlib.LinearAlgebra.Matrix.SinkhornScaling` — Sinkhorn / matrix-scaling
  existence (discrete Schrödinger potentials). STAGING (placeholder); see `FOUNDATIONS.md`.
* `ForMathlib.Analysis.ExpLogBounds` — exp/log real-analysis inequalities converting
  geometric logarithmic relative-error bounds into ordinary multiplicative relative-error bounds.
  STAGING (placeholder); used by the Franklin--Lorenz projective contraction port.
* `ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf` — finite positive-matrix Hilbert
  projective contraction coefficient (Birkhoff--Hopf), the Franklin--Lorenz convergence engine.
  STAGING (placeholder); see `LITERATURE_REFERENCES.md`.
* `ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute` — Eveson--Nussbaum finite-matrix
  proof spine: quadrant Hilbert formulas, convex-hull diameter, positive-matrix diameter,
  normalized `2 × 2` calculus, and assembly. STAGING (paper-route fanout surface).
* `ForMathlib.MeasureTheory.PathEmbedding` — a standard-Borel space with a countable
  point-separating measurable family embeds measurably into `ℕ→ℝ` with a measurable left
  inverse (Lusin–Souslin); the concrete continuous-path (`C(T,ℝ)`) instance and the resulting
  KL-limit that discharges the embedding edge of the continuum energy identity. PROVED.
-/
import ForMathlib.MeasureTheory.DonskerVaradhan
import ForMathlib.MeasureTheory.TiltedKernel
import ForMathlib.MeasureTheory.DonskerVaradhanDual
import ForMathlib.MeasureTheory.KLConvex
import ForMathlib.MeasureTheory.MeasurableArgmax
import ForMathlib.MeasureTheory.Normalization
import ForMathlib.MeasureTheory.GaussianEntropy
import ForMathlib.Analysis.Supergradient
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.Coupling
import ForMathlib.OptimalTransport.ConverseLagrangian
import ForMathlib.OptimalTransport.SinkhornConverse
import ForMathlib.OptimalTransport.Convexity
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.OptimalTransport.DroValueFunction
import ForMathlib.OptimalTransport.StrongDualityGe
import ForMathlib.OptimalTransport.WeakDuality
import ForMathlib.Analysis.ExpLogBounds
import ForMathlib.LinearAlgebra.Matrix.SinkhornScaling
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf.PaperRoute
-- Vendored Kolmogorov extension theorem (Apache-2.0, RemyDegenne/kolmogorov_extension4);
-- see ForMathlib/KolmogorovExtension/README.md. Supplies `projectiveLimit` for the
-- continuum reference path measure.
import ForMathlib.KolmogorovExtension.KolmogorovExtension
-- The continuum reference path law R (Wiener measure), built via the vendored extension.
import ForMathlib.MeasureTheory.WienerMeasure
-- Measurable embedding of a standard-Borel (continuous-)path space into `ℕ→ℝ` with measurable left
-- inverse; discharges the embedding edge of the continuum energy identity for continuous-path models.
import ForMathlib.MeasureTheory.PathEmbedding
-- Absolute continuity from a uniformly-integrable density martingale (Kakutani/Doob `≪`-direction);
-- the regularity input `P^u ≪ R` for the (deterministic) continuum energy identity, Itô-free.
-- Plus: automatic martingale property of consistent local densities, and the L²-bound ⇒ UI bridge.
import ForMathlib.MeasureTheory.AbsoluteContinuityMartingale
-- `Measure.pi` of `withDensity` factors, `withDensity` through a measurable equiv, and the
-- finite-product Tonelli `lintegral_pi_prod` (the Gaussian Cameron–Martin density bricks).
import ForMathlib.MeasureTheory.PiWithDensity
-- Sequence-model Cameron-Martin staging: iid Gaussian sequence law, prefix marginals,
-- shift/restriction interface, and finite-prefix density process.
import ForMathlib.MeasureTheory.GaussianCameronMartin
