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
`𝔼_γ[c(x, y)] + κ · KL(γ ‖ μ̂ ⊗ νref)`.

⚠ **Parametrized by the transport cost `c`, and it must be.** Wang–Gao–Xie Definition 1 states the
entropic ball for a general cost. Hard-wiring `‖x − y‖²` here while a downstream theorem quantifies
over its own `c` silently couples a *quadratic* ball to a *`c`*-budget, and the resulting hypothesis
is not jointly satisfiable in the real problem — an edge that fails AGENTS.md §6's honesty test.
`Drsb` instantiates `c := sqCost`.

⚠ The entropic reference is `μ̂ ⊗ νref` — the **nominal times an EXTERNAL reference `νref`**
(the measure the worst-case is a.c. wrt: Lebesgue/Gaussian/counting), exactly as
Wang–Gao–Xie **Definition 1** (`prose/sinkhorn-dro-duality.md`). It is NOT the product of
the two coupling marginals; the external `νref` is what appears in the dual's
log-partition `𝔼_{z∼νref}[e^{(f−λc)/(λκ)}]`, so ball and dual must share it. (An earlier
version used `μ ⊗ μ̂` — the product of marginals — which mismatched the dual; see the audit
note in `prose/sinkhorn-dro-duality.md` / AGENTS.md §6.) -/
noncomputable def sinkhornObjective (c : X → X → ℝ) (κ : ℝ) (μhat νref : ProbabilityMeasure X)
    (γ : ProbabilityMeasure (X × X)) : ℝ :=
  couplingCost c γ + κ * klReal (γ : Measure (X × X)) (prodMeasure μhat νref)

/-! ### The `ℝ≥0∞`-valued Sinkhorn objective

`sinkhornObjective` above is a **real** number, and both of its summands lose information on
their bad branch: `couplingCost2` is a Bochner integral (junk `0` when the cost is not
integrable) and `klReal` is `(klDiv · ·).toReal` (junk `0` when `klDiv = ∞`, i.e. exactly when
the coupling is *singular* against `μ̂ ⊗ ν`). Taking the infimum of that real quantity therefore
lets a singular coupling — the worst possible one — score `0` and drag `W_{κ,ν}` down to nothing.

The `ℝ≥0∞`-valued objective below has no bad branch: a non-integrable cost gives `∫⁻ = ∞` and a
singular coupling gives `klDiv = ∞`, so both correctly score `⊤` and drop out of the infimum.
`Wkappa` is defined from *this* one, and `sinkhornObjective` is recovered as its `toReal`
whenever the objective is finite (`sinkhornObjective_eq_toReal_of_ne_top`). -/

/-- `ℝ≥0∞`-valued transport cost of a coupling, `∫⁻ ofReal (c x y) dπ`. Unlike `couplingCost`
this is `∞`, not `0`, when the cost fails to be integrable. -/
noncomputable def couplingCostENN (c : X → X → ℝ) (π : ProbabilityMeasure (X × X)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂(π : Measure (X × X))

/-- `ℝ≥0∞`-valued squared-Euclidean transport cost of a coupling. -/
noncomputable def couplingCost2ENN (π : ProbabilityMeasure (X × X)) : ℝ≥0∞ :=
  couplingCostENN (fun x y => ‖x - y‖ ^ 2) π

/-- **Sinkhorn objective, `ℝ≥0∞`-valued** — `𝔼_γ[c(x,y)] + κ·KL(γ ‖ μ̂⊗ν)` with no `toReal`.
A singular `γ` scores `⊤` here, as it must. -/
noncomputable def sinkhornObjectiveENN (c : X → X → ℝ) (κ : ℝ) (μhat νref : ProbabilityMeasure X)
    (γ : ProbabilityMeasure (X × X)) : ℝ≥0∞ :=
  couplingCostENN c γ
    + ENNReal.ofReal κ * InformationTheory.klDiv (γ : Measure (X × X)) (prodMeasure μhat νref)

/-- **Sinkhorn discrepancy** `W_{κ,ν}(μ̂, μ) = inf_{γ ∈ Π(μ̂, μ)} 𝔼_γ[‖x−y‖²] + κ·KL(γ ‖ μ̂⊗ν)`
from the nominal `μhat` to a candidate `μ`, with external reference `νref` (Wang–Gao–Xie
Def 1; `κ` = entropic regularizer). The coupling has `μhat` as first marginal (the
disintegration/conditioning variable) and `μ` as second.

`ℝ≥0∞`-valued, over `sinkhornObjectiveENN`: the infimum must not be reachable by singular
couplings, whose real objective is the junk value `0`. -/
noncomputable def Wkappa (c : X → X → ℝ) (κ : ℝ) (νref μhat μ : ProbabilityMeasure X) : ℝ≥0∞ :=
  ⨅ γ ∈ couplings μhat μ, sinkhornObjectiveENN c κ μhat νref γ

/-- **Sinkhorn ambiguity ball** `𝓑^ν_{ε,κ}(μ̂) = { μ : W_{κ,ν}(μ̂, μ) ≤ ε }` around the
nominal `μhat`, with external reference `νref` (`κ` = regularizer, `ε` = radius).

Stated as "`W_{κ,ν}` is finite and its value is `≤ ε`" rather than `W_{κ,ν} ≤ ENNReal.ofReal ε`.
The two agree for `ε ≥ 0`, but `ENNReal.ofReal` sends every negative radius to `0`, so the
`ofReal` form would make the ball of a *negative* radius equal `{μ | W_{κ,ν} = 0}` — nonempty in
the degenerate case `μ̂ = ν = μ = δₐ`, which would falsify
`WangGaoXie2023.primal_feasible_radius_nonneg`. This form keeps a negative-radius ball empty. -/
def sinkhornBall (c : X → X → ℝ) (μhat νref : ProbabilityMeasure X) (κ ε : ℝ) :
    Set (ProbabilityMeasure X) :=
  { μ | Wkappa c κ νref μhat μ ≠ ⊤ ∧ (Wkappa c κ νref μhat μ).toReal ≤ ε }

/-- The DRO worst-case value of an objective `f` over an ambiguity set `𝓐`:
`sup_{μ ∈ 𝓐} 𝔼_μ[f]`. -/
noncomputable def droValue (𝓐 : Set (ProbabilityMeasure X)) (f : X → ℝ) : ℝ :=
  sSup { r : ℝ | ∃ μ : ProbabilityMeasure X, μ ∈ 𝓐 ∧ r = expect μ f }

end ForMathlib.OT
