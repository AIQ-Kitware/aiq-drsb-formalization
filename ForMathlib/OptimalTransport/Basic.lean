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

/-- **Sinkhorn (entropic-OT) objective** for a coupling `γ` of the nominal `μhat` (first
marginal) with a candidate, at regularizer `κ`, against an **external reference `νref`**:
`𝔼_γ[‖x − y‖²] + κ · KL(γ ‖ μ̂ ⊗ νref)`.

⚠ The entropic reference is `μ̂ ⊗ νref` — the **nominal times an EXTERNAL reference `νref`**
(the measure the worst-case is a.c. wrt: Lebesgue/Gaussian/counting), exactly as
Wang–Gao–Xie **Definition 1** (`prose/sinkhorn-dro-duality.md`). It is NOT the product of
the two coupling marginals; the external `νref` is what appears in the dual's
log-partition `𝔼_{z∼νref}[e^{(f−λc)/(λκ)}]`, so ball and dual must share it. (An earlier
version used `μ ⊗ μ̂` — the product of marginals — which mismatched the dual; see the audit
note in `prose/sinkhorn-dro-duality.md` / AGENTS.md §6.) -/
noncomputable def sinkhornObjective (κ : ℝ) (μhat νref : ProbabilityMeasure X)
    (γ : ProbabilityMeasure (X × X)) : ℝ :=
  couplingCost2 γ + κ * klReal (γ : Measure (X × X)) (prodMeasure μhat νref)

/-- **Sinkhorn discrepancy** `W_{κ,ν}(μ̂, μ) = inf_{γ ∈ Π(μ̂, μ)} 𝔼_γ[‖x−y‖²] + κ·KL(γ ‖ μ̂⊗ν)`
from the nominal `μhat` to a candidate `μ`, with external reference `νref` (Wang–Gao–Xie
Def 1; `κ` = entropic regularizer). The coupling has `μhat` as first marginal (the
disintegration/conditioning variable) and `μ` as second. -/
noncomputable def Wkappa (κ : ℝ) (νref μhat μ : ProbabilityMeasure X) : ℝ :=
  sInf { r : ℝ | ∃ γ : ProbabilityMeasure (X × X),
    γ ∈ couplings μhat μ ∧ r = sinkhornObjective κ μhat νref γ }

/-- **Sinkhorn ambiguity ball** `𝓑^ν_{ε,κ}(μ̂) = { μ : W_{κ,ν}(μ̂, μ) ≤ ε }` around the
nominal `μhat`, with external reference `νref` (`κ` = regularizer, `ε` = radius). -/
def sinkhornBall (μhat νref : ProbabilityMeasure X) (κ ε : ℝ) :
    Set (ProbabilityMeasure X) :=
  { μ | Wkappa κ νref μhat μ ≤ ε }

/-- The DRO worst-case value of an objective `f` over an ambiguity set `𝓐`:
`sup_{μ ∈ 𝓐} 𝔼_μ[f]`. -/
noncomputable def droValue (𝓐 : Set (ProbabilityMeasure X)) (f : X → ℝ) : ℝ :=
  sSup { r : ℝ | ∃ μ : ProbabilityMeasure X, μ ∈ 𝓐 ∧ r = expect μ f }

end ForMathlib.OT
