/-
# Concrete Wiener dyadic grid and projection maps

This module contains only carrier/grid definitions and finite dyadic projection
calculus for the concrete nonnegative-time Wiener path space.
-/

import ChenGeorgiouPavon2021.Continuum.IntervalPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- Nonnegative-time real path space used by the concrete `wienerMeasure` construction.

The CGP-facing M4 interface keeps `RealPath := Path ℝ` so endpoint and path-law
statements remain stable.  The vendored Kolmogorov construction of standard Wiener measure,
however, naturally lives on `NNReal → ℝ`.  This parallel nonnegative-time staging namespace is the
place where we discharge the "real Wiener measure satisfies the finite-dimensional standard-normal
increment law" capstone before transporting it back to whatever final CGP path representation is
chosen. -/
abbrev WienerRealPath : Type := NNReal → ℝ

/-- Dyadic time `i / 2ⁿ` as a nonnegative real. -/
noncomputable def dyadicTimeNNReal (level i : ℕ) : NNReal :=
  ⟨(i : ℝ) / ((2 : ℝ) ^ level), by positivity⟩

/-- Raw dyadic increment on the concrete nonnegative-time Wiener path space. -/
noncomputable def wienerDyadicIncrement (level : ℕ) (ω : WienerRealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  ω (dyadicTimeNNReal level (i.1 + 1)) - ω (dyadicTimeNNReal level i.1)

/-- Normalized dyadic increment on `NNReal → ℝ` paths. -/
noncomputable def normalizedWienerDyadicIncrement (level : ℕ) (ω : WienerRealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  wienerDyadicIncrement level ω i / Real.sqrt (dyadicMesh level)

/-- Vector of normalized dyadic increments for the concrete nonnegative-time Wiener path space. -/
noncomputable def normalizedWienerDyadicIncrementMap (level : ℕ) :
    WienerRealPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => normalizedWienerDyadicIncrement level ω i


/-- The dyadic endpoint grid `{0, 1/2ⁿ, ..., 1}` as a finite set of nonnegative times. -/
noncomputable def wienerDyadicGrid (level : ℕ) : Finset NNReal :=
  (Finset.range (2 ^ level + 1)).image (fun i : ℕ => dyadicTimeNNReal level i)

/-- Dyadic endpoint times belong to the level grid. -/
lemma dyadicTimeNNReal_mem_wienerDyadicGrid
    (level i : ℕ) (hi : i ≤ 2 ^ level) :
    dyadicTimeNNReal level i ∈ wienerDyadicGrid level := by
  classical
  refine Finset.mem_image.mpr ?_
  refine ⟨i, ?_, rfl⟩
  simpa [Nat.lt_succ_iff] using hi

/-- A dyadic endpoint, bundled as an element of the dyadic grid. -/
noncomputable def wienerDyadicGridPoint (level i : ℕ) (hi : i ≤ 2 ^ level) :
    wienerDyadicGrid level :=
  ⟨dyadicTimeNNReal level i, dyadicTimeNNReal_mem_wienerDyadicGrid level i hi⟩

/-- Normalized dyadic increment as a linear map out of the finite dyadic endpoint vector. -/
noncomputable def normalizedWienerDyadicIncrementFromGrid (level : ℕ) :
    ((wienerDyadicGrid level) → ℝ) → (Fin (2 ^ level) → ℝ) :=
  fun x i =>
    (x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
        - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2)))
      / Real.sqrt (dyadicMesh level)

/-- The finite-grid normalized-increment map factors through restriction to the dyadic endpoint grid. -/
theorem normalizedWienerDyadicIncrementMap_eq_fromGrid (level : ℕ) :
    normalizedWienerDyadicIncrementMap level
      = normalizedWienerDyadicIncrementFromGrid level ∘
          (fun ω : WienerRealPath => (wienerDyadicGrid level).restrict ω) := by
  funext ω i
  simp [normalizedWienerDyadicIncrementMap, normalizedWienerDyadicIncrementFromGrid,
    normalizedWienerDyadicIncrement, wienerDyadicIncrement, Function.comp,
    wienerDyadicGridPoint]

end ChenGeorgiouPavon2021
