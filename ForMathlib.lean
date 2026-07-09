/-
# ForMathlib — paper-agnostic staging library

Reusable results, restated in Mathlib idiom, that the DRSB paper libraries import.
These are potential upstream Mathlib contributions (some already have complete
proofs in `reference/WellKnown.lean`; they are re-stated here with placeholder while we
audit statements against the papers, per the first-pass "statements only" policy).

One file per proposed Mathlib destination area:
* `ForMathlib.MeasureTheory.DonskerVaradhan` — the DV inequality / Gibbs variational
  identity (root fact under the Sinkhorn-DRO dual).
* `ForMathlib.MeasureTheory.Normalization` — normalize a finite nonzero measure to a
  probability measure (the `(μ univ)⁻¹ • μ` construction).
* `ForMathlib.MeasureTheory.GaussianEntropy` — Cameron–Martin relative entropy of a
  finite-dimensional Gaussian shift (`KL(N(·+h) ‖ N) = ½‖h‖²`), vendored from
  `mrdouglasny/gibbs-variational` (Apache-2.0; see the file header + README), plus the
  Euler–Maruyama discrete energy identity built on it.
* `ForMathlib.OptimalTransport.Basic` — the shared OT / DRO vocabulary (couplings,
  transport cost, Wasserstein-2 and Sinkhorn ambiguity balls, KL, DRO worst-case).
* `ForMathlib.OptimalTransport.WeakDuality` — the per-coupling Lagrangian bound (the
  always-true `≤` half of OT-DRO duality). STAGING (placeholder); see `FOUNDATIONS.md`.
* `ForMathlib.LinearAlgebra.Matrix.SinkhornScaling` — Sinkhorn / matrix-scaling
  existence (discrete Schrödinger potentials). STAGING (placeholder); see `FOUNDATIONS.md`.
* `ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf` — finite positive-matrix Hilbert
  projective contraction coefficient (Birkhoff--Hopf), the Franklin--Lorenz convergence engine.
  STAGING (placeholder); see `LITERATURE_REFERENCES.md`.
* `ForMathlib.MeasureTheory.PathEmbedding` — a standard-Borel space with a countable
  point-separating measurable family embeds measurably into `ℕ→ℝ` with a measurable left
  inverse (Lusin–Souslin); the concrete continuous-path (`C(T,ℝ)`) instance and the resulting
  KL-limit that discharges the embedding edge of the continuum energy identity. PROVED.
-/
import ForMathlib.MeasureTheory.DonskerVaradhan
import ForMathlib.MeasureTheory.Normalization
import ForMathlib.MeasureTheory.GaussianEntropy
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.WeakDuality
import ForMathlib.LinearAlgebra.Matrix.SinkhornScaling
import ForMathlib.LinearAlgebra.Matrix.BirkhoffHopf
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
