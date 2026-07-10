/-
# Coupling existence, near-optimal plans, and quadratic-cost integrability (Mathlib-staging)

The elementary facts about `couplings` / `otCost` that let a DRO cost bound be stated
**without** an optimal-transport *attainment* hypothesis.

Three ingredients, none of them in Mathlib (which has no Kantorovich layer at all):

1. `couplings_nonempty` — the independent coupling `μ ⊗ ν` is always a coupling, so the
   value set `{ 𝔼_π[c] : π ∈ Π(μ,ν) }` whose `sInf` defines `otCost` is nonempty.
2. `exists_coupling_couplingCost_lt` — hence `otCost c μ ν < b` yields an explicit
   *near-optimal* plan `π` with `𝔼_π[c] < b`. This is the honest replacement for
   "the infimum is attained": the `sInf` gives `ε + η` for every `η > 0`, never `ε`.
3. `integrable_normSq_sub_of_mem_couplings` — **finite second moments of the marginals
   force every coupling's quadratic cost to be integrable**, via
   `‖x − y‖² ≤ 2‖x‖² + 2‖y‖²` and the marginal pushforward identities.

Together these discharge the "OT-attainment edge" that a Wasserstein-DRO weak-duality
bound would otherwise have to assume (see `Drsb.wdrsb_cost_bound`): the bound follows
from a near-optimal plan plus a limit `η ↓ 0`, and the plan's cost is integrable for
free once the marginals have second moments.

Why (3) is load-bearing and not bookkeeping: `couplingCost` is a **Bochner** integral, so
a coupling whose cost is not integrable silently contributes the junk value `0` to the
`sInf`. By the converse lemma `integrable_normSq_of_mem_couplings_of_integrable_cost`, if
the nominal `ν` has a finite second moment and `μ` does not, then *no* coupling of the two
has integrable cost — so every one of them contributes `0`, and `W₂²(μ, ν) = 0`. Such a `μ`
lies in the Wasserstein ball of **every** radius: for it, ball membership carries no
information at all, and there is no integrable-cost plan for a Lagrangian bound to run on.
The moment hypotheses are exactly what excludes that degenerate membership.

`diagCoupling` additionally gives `W₂²(μ, μ) ≤ 0`, so a Wasserstein ball of nonnegative
radius is nonempty without hypothesis (`mem_wassersteinBall_self`).
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ForMathlib.OT

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-! ## The independent coupling: `Π(μ, ν)` is never empty -/

/-- The **independent (product) coupling** `μ ⊗ ν ∈ Π(μ, ν)`. -/
noncomputable def prodCoupling (μ ν : ProbabilityMeasure X) : ProbabilityMeasure (X × X) :=
  ⟨(μ : Measure X).prod (ν : Measure X), by infer_instance⟩

omit [NormedAddCommGroup X] in
theorem prodCoupling_mem_couplings (μ ν : ProbabilityMeasure X) :
    prodCoupling μ ν ∈ couplings μ ν :=
  ⟨Measure.fst_prod, Measure.snd_prod⟩

omit [NormedAddCommGroup X] in
/-- **The coupling set is always nonempty** (witnessed by `μ ⊗ ν`). Hence the value set
defining `otCost` is nonempty, which is what makes `sInf` reasoning about it usable. -/
theorem couplings_nonempty (μ ν : ProbabilityMeasure X) : (couplings μ ν).Nonempty :=
  ⟨_, prodCoupling_mem_couplings μ ν⟩

omit [NormedAddCommGroup X] in
/-- The set of coupling-cost *values* whose `sInf` is `otCost c μ ν`. -/
theorem couplingCostSet_nonempty (c : X → X → ℝ) (μ ν : ProbabilityMeasure X) :
    Set.Nonempty { r : ℝ | ∃ π : ProbabilityMeasure (X × X),
      π ∈ couplings μ ν ∧ r = couplingCost c π } := by
  obtain ⟨π, hπ⟩ := couplings_nonempty μ ν
  exact ⟨couplingCost c π, π, hπ, rfl⟩

omit [NormedAddCommGroup X] in
/-- **Near-optimal transport plans exist.** If the optimal transport cost is `< b`, some
explicit coupling has cost `< b`.

This is the *usable* content of `otCost c μ ν ≤ ε`: it never produces a plan of cost
`≤ ε` (that is the attainment theorem, and it is false without compactness/lower
semicontinuity hypotheses), but it produces one of cost `< ε + η` for every `η > 0`.
Downstream bounds recover the sharp constant by letting `η ↓ 0`. -/
theorem exists_coupling_couplingCost_lt (c : X → X → ℝ) (μ ν : ProbabilityMeasure X) (b : ℝ)
    (h : otCost c μ ν < b) :
    ∃ π ∈ couplings μ ν, couplingCost c π < b := by
  rw [otCost] at h
  obtain ⟨r, ⟨π, hπ, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt (couplingCostSet_nonempty c μ ν) h
  exact ⟨π, hπ, hlt⟩

/-! ## Second moments ⟹ quadratic cost is integrable under every coupling -/

/-- Under any coupling of `μ` with `ν`, the first coordinate's square-norm is integrable
as soon as `μ` has a finite second moment. -/
theorem integrable_normSq_fst_of_mem_couplings [OpensMeasurableSpace X]
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)) (hπ : π ∈ couplings μ ν)
    (hμ2 : Integrable (fun x => ‖x‖ ^ 2) (μ : Measure X)) :
    Integrable (fun z : X × X => ‖z.1‖ ^ 2) (π : Measure (X × X)) := by
  have hfst : (μ : Measure X) = Measure.map Prod.fst (π : Measure (X × X)) := hπ.1.symm
  have hae : AEStronglyMeasurable (fun x : X => ‖x‖ ^ 2)
      (Measure.map Prod.fst (π : Measure (X × X))) := hfst ▸ hμ2.1
  exact (integrable_map_measure hae measurable_fst.aemeasurable).mp (hfst ▸ hμ2)

/-- Under any coupling of `μ` with `ν`, the second coordinate's square-norm is integrable
as soon as `ν` has a finite second moment. -/
theorem integrable_normSq_snd_of_mem_couplings [OpensMeasurableSpace X]
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)) (hπ : π ∈ couplings μ ν)
    (hν2 : Integrable (fun x => ‖x‖ ^ 2) (ν : Measure X)) :
    Integrable (fun z : X × X => ‖z.2‖ ^ 2) (π : Measure (X × X)) := by
  have hsnd : (ν : Measure X) = Measure.map Prod.snd (π : Measure (X × X)) := hπ.2.symm
  have hae : AEStronglyMeasurable (fun x : X => ‖x‖ ^ 2)
      (Measure.map Prod.snd (π : Measure (X × X))) := hsnd ▸ hν2.1
  exact (integrable_map_measure hae measurable_snd.aemeasurable).mp (hsnd ▸ hν2)

/-- **Finite second moments of the marginals ⟹ every coupling has integrable quadratic
cost.** Dominate `‖x − y‖² ≤ 2‖x‖² + 2‖y‖²` and read each square-norm off its marginal.

This is what makes the OT-attainment edge of a `W₂²` cost bound unnecessary: the
integrability side condition on the witnessing plan, which the edge used to carry, is a
theorem about the marginals alone. -/
theorem integrable_normSq_sub_of_mem_couplings [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)) (hπ : π ∈ couplings μ ν)
    (hμ2 : Integrable (fun x => ‖x‖ ^ 2) (μ : Measure X))
    (hν2 : Integrable (fun x => ‖x‖ ^ 2) (ν : Measure X)) :
    Integrable (fun z : X × X => ‖z.1 - z.2‖ ^ 2) (π : Measure (X × X)) := by
  have h1 := integrable_normSq_fst_of_mem_couplings μ ν π hπ hμ2
  have h2 := integrable_normSq_snd_of_mem_couplings μ ν π hπ hν2
  have hdom : Integrable (fun z : X × X => 2 * ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2)
      (π : Measure (X × X)) := (h1.const_mul 2).add (h2.const_mul 2)
  refine hdom.mono' (((measurable_fst.sub measurable_snd).norm).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith [norm_sub_le z.1 z.2, norm_nonneg (z.1 - z.2), norm_nonneg z.1, norm_nonneg z.2,
    sq_nonneg (‖z.1‖ - ‖z.2‖)]

/-- **Converse of `integrable_normSq_sub_of_mem_couplings`.** A single coupling of
integrable quadratic cost transfers a finite second moment from one marginal to the other,
by `‖x‖² ≤ 2‖x − y‖² + 2‖y‖²`.

This is what makes the second-moment hypotheses *no stronger* than an optimal-transport
edge: any hypothesis supplying an integrable-cost plan between `μ` and a nominal `ν` of
finite second moment already entails that `μ` has one. -/
theorem integrable_normSq_of_mem_couplings_of_integrable_cost [OpensMeasurableSpace X]
    [MeasurableSub₂ X]
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)) (hπ : π ∈ couplings μ ν)
    (hcost : Integrable (fun z : X × X => ‖z.1 - z.2‖ ^ 2) (π : Measure (X × X)))
    (hν2 : Integrable (fun x => ‖x‖ ^ 2) (ν : Measure X)) :
    Integrable (fun x => ‖x‖ ^ 2) (μ : Measure X) := by
  have h2 := integrable_normSq_snd_of_mem_couplings μ ν π hπ hν2
  have hdom : Integrable (fun z : X × X => 2 * ‖z.1 - z.2‖ ^ 2 + 2 * ‖z.2‖ ^ 2)
      (π : Measure (X × X)) := (hcost.const_mul 2).add (h2.const_mul 2)
  have hfstπ : Integrable (fun z : X × X => ‖z.1‖ ^ 2) (π : Measure (X × X)) := by
    refine hdom.mono' (measurable_fst.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_sub_le z.1 z.2, norm_nonneg (z.1 - z.2), norm_nonneg z.1, norm_nonneg z.2,
      sq_nonneg (‖z.1 - z.2‖ - ‖z.2‖), norm_le_norm_add_norm_sub' z.1 z.2]
  have hfst : (μ : Measure X) = Measure.map Prod.fst (π : Measure (X × X)) := hπ.1.symm
  have hae : AEStronglyMeasurable (fun x : X => ‖x‖ ^ 2)
      (Measure.map Prod.fst (π : Measure (X × X))) :=
    (measurable_norm.pow_const 2).aestronglyMeasurable
  exact hfst ▸ (integrable_map_measure hae measurable_fst.aemeasurable).mpr hfstπ

/-! ## The diagonal coupling: Wasserstein balls are nonempty -/

/-- The **diagonal coupling** `(id, id)_# μ ∈ Π(μ, μ)`, of zero quadratic cost. -/
noncomputable def diagCoupling (μ : ProbabilityMeasure X) : ProbabilityMeasure (X × X) :=
  ⟨(μ : Measure X).map (fun x => (x, x)),
    Measure.isProbabilityMeasure_map (measurable_id.prodMk measurable_id).aemeasurable⟩

omit [NormedAddCommGroup X] in
theorem diagCoupling_mem_couplings (μ : ProbabilityMeasure X) :
    diagCoupling μ ∈ couplings μ μ := by
  have hdiag : Measurable (fun x : X => (x, x)) := measurable_id.prodMk measurable_id
  constructor
  · show Measure.map Prod.fst ((μ : Measure X).map (fun x => (x, x))) = (μ : Measure X)
    rw [Measure.map_map measurable_fst hdiag]; simp [Function.comp_def]
  · show Measure.map Prod.snd ((μ : Measure X).map (fun x => (x, x))) = (μ : Measure X)
    rw [Measure.map_map measurable_snd hdiag]; simp [Function.comp_def]

/-- `W₂²(μ, μ) ≤ 0`, witnessed by the diagonal coupling. -/
theorem W2sq_self_le_zero [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (μ : ProbabilityMeasure X) : W2sq μ μ ≤ 0 := by
  have hdiag : Measurable (fun x : X => (x, x)) := measurable_id.prodMk measurable_id
  have hcost : couplingCost (fun x y : X => ‖x - y‖ ^ 2) (diagCoupling μ) = 0 := by
    show ∫ z : X × X, ‖z.1 - z.2‖ ^ 2 ∂((μ : Measure X).map (fun x => (x, x))) = 0
    rw [integral_map (f := fun z : X × X => ‖z.1 - z.2‖ ^ 2) hdiag.aemeasurable
      (((measurable_fst.sub measurable_snd).norm).pow_const 2).aestronglyMeasurable]
    simp
  refine le_of_le_of_eq (csInf_le ⟨0, ?_⟩ ⟨diagCoupling μ, diagCoupling_mem_couplings μ, rfl⟩) hcost
  rintro r ⟨π, _, rfl⟩
  exact integral_nonneg fun z => by positivity

/-- **A Wasserstein ball of nonnegative radius contains its own centre**, so it is
nonempty without hypothesis. -/
theorem mem_wassersteinBall_self [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (μ : ProbabilityMeasure X) (ε : ℝ) (hε : 0 ≤ ε) : μ ∈ wassersteinBall μ ε :=
  le_trans (W2sq_self_le_zero μ) hε

end ForMathlib.OT
