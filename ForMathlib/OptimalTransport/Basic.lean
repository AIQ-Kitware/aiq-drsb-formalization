/-
# Optimal-transport / DRO primitives (Mathlib-staging, shared vocabulary)

Kantorovich couplings, transport costs, the Wasserstein-2 and Sinkhorn (entropic-OT)
ambiguity balls, and the real-valued KL wrapper. This is the *shared vocabulary* the
DRSB DRO paper libraries (`BlanchetMurthy2019`, `GaoKleywegt2023`,
`MohajerinEsfahaniKuhn2018`, `WangGaoXie2023`) and the `Drsb` capstone speak, so the
strong-duality statements compose. Object definitions only — no theorems here.

Adapted from the (reference-only) `reference/V4.lean` object layer, cleaned and
generalized (arbitrary transport cost `c` for Blanchet–Murthy). The *theorem
statements* that use these live in the per-paper libraries and are re-derived from
`../prose/`, not from `reference/`.
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace ForMathlib.OT

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-- Expectation `𝔼_μ[f] = ∫ f dμ` for a probability measure `μ` and real `f`. -/
noncomputable def expect (μ : ProbabilityMeasure X) (f : X → ℝ) : ℝ :=
  ∫ x, f x ∂(μ : Measure X)

/-- Real-valued Kullback–Leibler divergence, `KL(μ‖ν) = (klDiv μ ν).toReal`. The
paper statements treat KL as a real number, which implicitly assumes finiteness
(`klDiv μ ν ≠ ⊤`); add that hypothesis where arithmetic on KL is needed. -/
noncomputable def klReal (μ ν : Measure X) : ℝ :=
  (InformationTheory.klDiv μ ν).toReal

/-- The set of couplings `Π(μ, ν)`: probability measures on `X × X` with first
marginal `μ` and second marginal `ν`. -/
def couplings (μ ν : ProbabilityMeasure X) : Set (ProbabilityMeasure (X × X)) :=
  { π | Measure.map Prod.fst (π : Measure (X × X)) = (μ : Measure X)
      ∧ Measure.map Prod.snd (π : Measure (X × X)) = (ν : Measure X) }

/-- Transport cost of a coupling under a (measurable) cost `c : X → X → ℝ`:
`𝔼_π[c(x, y)]`. -/
noncomputable def couplingCost (c : X → X → ℝ) (π : ProbabilityMeasure (X × X)) : ℝ :=
  ∫ z, c z.1 z.2 ∂(π : Measure (X × X))

/-- Optimal transport cost `T_c(μ, ν) = inf_{π ∈ Π(μ,ν)} 𝔼_π[c]` for a general cost
`c`. This is the Kantorovich primal; Blanchet–Murthy state DRO duality for this
general `c`. -/
noncomputable def otCost (c : X → X → ℝ) (μ ν : ProbabilityMeasure X) : ℝ :=
  sInf { r : ℝ | ∃ π : ProbabilityMeasure (X × X),
    π ∈ couplings μ ν ∧ r = couplingCost c π }

/-- Squared-Euclidean transport cost of a coupling, `𝔼_π[‖x − y‖²]`. -/
noncomputable def couplingCost2 (π : ProbabilityMeasure (X × X)) : ℝ :=
  couplingCost (fun x y => ‖x - y‖ ^ 2) π

/-- Wasserstein-2 squared: `W₂²(μ, ν) = inf_{π ∈ Π(μ,ν)} 𝔼_π[‖x − y‖²]`. -/
noncomputable def W2sq (μ ν : ProbabilityMeasure X) : ℝ :=
  otCost (fun x y => ‖x - y‖ ^ 2) μ ν

/-- Wasserstein ambiguity ball `𝓜_ε(μ̂) = { μ : W₂²(μ, μ̂) ≤ ε }`. -/
def wassersteinBall (μhat : ProbabilityMeasure X) (ε : ℝ) : Set (ProbabilityMeasure X) :=
  { μ | W2sq μ μhat ≤ ε }

/-- Product measure `μ ⊗ ν` on `X × X`. -/
noncomputable def prodMeasure (μ ν : ProbabilityMeasure X) : Measure (X × X) :=
  (μ : Measure X).prod (ν : Measure X)

/-- Sinkhorn (entropic-OT) objective for a fixed coupling `π`, at regularization
`κ`: `𝔼_π[‖x − y‖²] + κ · KL(π ‖ μ ⊗ ν)`. -/
noncomputable def sinkhornObjective (κ : ℝ) (μ ν : ProbabilityMeasure X)
    (π : ProbabilityMeasure (X × X)) : ℝ :=
  couplingCost2 π + κ * klReal (π : Measure (X × X)) (prodMeasure μ ν)

/-- Entropic-OT / Sinkhorn discrepancy
`W_κ(μ, ν) = inf_{π ∈ Π(μ,ν)} 𝔼_π[‖x−y‖²] + κ·KL(π ‖ μ⊗ν)`. (Paper convention: `κ`
is the entropic regularizer.) -/
noncomputable def Wkappa (κ : ℝ) (μ ν : ProbabilityMeasure X) : ℝ :=
  sInf { r : ℝ | ∃ π : ProbabilityMeasure (X × X),
    π ∈ couplings μ ν ∧ r = sinkhornObjective κ μ ν π }

/-- Sinkhorn ambiguity ball `𝓜^S_ε(μ̂) = { μ : W_κ(μ, μ̂) ≤ ε }`. (Paper convention:
`ε` is the ball radius.) -/
def sinkhornBall (μhat : ProbabilityMeasure X) (κ ε : ℝ) : Set (ProbabilityMeasure X) :=
  { μ | Wkappa κ μ μhat ≤ ε }

/-- The DRO worst-case value of an objective `f` over an ambiguity set `𝓐`:
`sup_{μ ∈ 𝓐} 𝔼_μ[f]`. -/
noncomputable def droValue (𝓐 : Set (ProbabilityMeasure X)) (f : X → ℝ) : ℝ :=
  sSup { r : ℝ | ∃ μ : ProbabilityMeasure X, μ ∈ 𝓐 ∧ r = expect μ f }

end ForMathlib.OT
