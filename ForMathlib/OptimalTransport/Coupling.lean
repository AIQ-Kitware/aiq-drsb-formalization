/-
# Couplings, near-optimal plans, and the `ℝ≥0∞` Sinkhorn discrepancy (Mathlib-staging)

The facts about `couplings`, `otCost`, and `Wkappa` used to derive the DRO cost bounds from
near-optimal transport plans and finite-cost Sinkhorn plans.

Everything except the explicitly quadratic section at the end is stated between **two** measurable
spaces `α`, `β` under a cost `c : α → β → ℝ`, with no algebra or topology on either — the shape the
theory actually has, and the shape an upstream Mathlib API should have.

## Wasserstein half

1. `couplings_nonempty` — the independent coupling `μ ⊗ ν` is always a coupling, so the value set
   `{ 𝔼_π[c] : π ∈ Π(μ,ν) }` whose `sInf` defines `otCost` is nonempty.
2. `exists_coupling_couplingCost_lt` — hence `otCost c μ ν < b` yields an explicit *near-optimal*
   plan `π` with `𝔼_π[c] < b`.  This is the approximation property of an infimum and does not
   require attainment.
3. `integrable_normSq_sub_of_mem_couplings` — **finite second moments of the marginals force every
   coupling's quadratic cost to be integrable**, via `‖x − y‖² ≤ 2‖x‖² + 2‖y‖²`; and its converse,
   which transfers a finite second moment back through any finite-cost coupling.

Why (3) is load-bearing: `couplingCost` is a **Bochner** integral, so a coupling of non-integrable
cost silently contributes the junk value `0` to the `sInf`. If the nominal `ν` has a finite second
moment and `μ` does not, then *no* coupling of the two has integrable cost, every one contributes
`0`, and `W₂²(μ, ν) = 0` — such a `μ` lies in the Wasserstein ball of **every** radius. The moment
hypotheses are what exclude that degenerate membership. (`otCost` has not been refactored to
`ℝ≥0∞`; see `STATUS.md`.)

`diagCoupling` gives `W₂²(μ, μ) ≤ 0`, so a Wasserstein ball of nonnegative radius is nonempty
without hypothesis (`mem_wassersteinBall_self`).

## Sinkhorn half

`klReal` is `(klDiv · ·).toReal`, which maps an infinite divergence to zero.  The canonical
Sinkhorn discrepancy therefore uses the `ℝ≥0∞` objective `sinkhornObjectiveENN`, where singular
couplings have value `⊤` and do not act as finite competitors.

The theorem `exists_isSinkhornPlan_of_mem_sinkhornBall` extracts from ball membership, for every
`η > 0`, a coupling absolutely continuous with respect to `p₀ ⊗ ν`, with finite relative entropy
and objective at most `ε + η`.  `mem_sinkhornBall_reference` gives a concrete nonemptiness witness
under its radius condition.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ForMathlib.OT
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## The independent coupling: `Π(μ, ν)` is never empty -/

/-- The **independent (product) coupling** `μ ⊗ ν ∈ Π(μ, ν)`. -/
noncomputable def prodCoupling (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : ProbabilityMeasure (α × β) :=
  ⟨(μ : Measure α).prod (ν : Measure β), by infer_instance⟩

theorem prodCoupling_mem_couplings (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    prodCoupling μ ν ∈ couplings μ ν :=
  ⟨Measure.fst_prod, Measure.snd_prod⟩

/-- **The coupling set is always nonempty** (witnessed by `μ ⊗ ν`). Hence the value set
defining `otCost` is nonempty, which is what makes `sInf` reasoning about it usable. -/
theorem couplings_nonempty (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) : (couplings μ ν).Nonempty :=
  ⟨_, prodCoupling_mem_couplings μ ν⟩

/-- The set of coupling-cost *values* whose `sInf` is `otCost c μ ν`. -/
theorem couplingCostSet_nonempty (c : α → β → ℝ) (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    Set.Nonempty { r : ℝ | ∃ π : ProbabilityMeasure (α × β),
      π ∈ couplings μ ν ∧ r = couplingCost c π } := by
  obtain ⟨π, hπ⟩ := couplings_nonempty μ ν
  exact ⟨couplingCost c π, π, hπ, rfl⟩

/-- **Near-optimal transport plans exist.** If the optimal transport cost is `< b`, some
explicit coupling has cost `< b`.

This is the *usable* content of `otCost c μ ν ≤ ε`: it never produces a plan of cost
`≤ ε` (that is the attainment theorem, and it is false without compactness/lower
semicontinuity hypotheses), but it produces one of cost `< ε + η` for every `η > 0`.
Downstream bounds recover the sharp constant by letting `η ↓ 0`. -/
theorem exists_coupling_couplingCost_lt (c : α → β → ℝ) (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) (b : ℝ)
    (h : otCost c μ ν < b) :
    ∃ π ∈ couplings μ ν, couplingCost c π < b := by
  rw [otCost] at h
  obtain ⟨r, ⟨π, hπ, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt (couplingCostSet_nonempty c μ ν) h
  exact ⟨π, hπ, hlt⟩
/-! ## Why the Sinkhorn objective must be `ℝ≥0∞`-valued

`klReal` is `(klDiv · ·).toReal`, so it has a bad branch. The lemma below is the reason
`Wkappa` is defined from `sinkhornObjectiveENN` rather than from the real `sinkhornObjective`. -/

/-- **A singular pair has `klReal = 0`, not `klReal = ∞`.** `klDiv μ ν = ∞` when `μ ⋠ ν`, so
`toReal` collapses the *largest possible* divergence to the *smallest possible* real number.

Were `Wkappa` an infimum of the **real** `sinkhornObjective`, a coupling `γ` of infinite entropy
relative to `μ̂ ⊗ ν` would be scored as though it had *zero* entropy, and could drag the infimum
down to its cost alone — so `μ ∈ sinkhornBall` would carry no information about `μ`. Defining
`Wkappa` from `sinkhornObjectiveENN` scores such a `γ` as `⊤`, and it drops out of the infimum.
That is what makes `exists_isSinkhornPlan_of_mem_sinkhornBall` below a theorem. -/
theorem klReal_eq_zero_of_not_absolutelyContinuous {μ ν : Measure α} (h : ¬ μ ≪ ν) :
    klReal μ ν = 0 := by
  rw [klReal, InformationTheory.klDiv_of_not_ac h, ENNReal.toReal_top]
/-! ## `ℝ≥0∞` ↔ real bridge for the quadratic cost -/

/-- **A coupling of finite `ℝ≥0∞` cost has integrable cost.** The `ℝ≥0∞` cost has no bad branch, so
its finiteness *is* integrability — which is why an `IsSinkhornPlan` can carry `integrable_cost` as
a derived field rather than forcing its consumers to assume second moments. -/
theorem integrable_of_couplingCostENN_ne_top (c : α → β → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (hcm : Measurable fun z : α × β => c z.1 z.2)
    (π : ProbabilityMeasure (α × β)) (h : couplingCostENN c π ≠ ⊤) :
    Integrable (fun z : α × β => c z.1 z.2) (π : Measure (α × β)) := by
  refine ⟨hcm.aestronglyMeasurable, ?_⟩
  have hcongr : ∫⁻ z : α × β, ‖c z.1 z.2‖ₑ ∂(π : Measure (α × β)) = couplingCostENN c π :=
    lintegral_congr fun z => by rw [Real.enorm_eq_ofReal (hc _ _)]
  rw [HasFiniteIntegral, hcongr]
  exact lt_top_iff_ne_top.mpr h

/-- On a nonnegative measurable cost the Bochner cost is the `toReal` of the `ℝ≥0∞` cost. -/
theorem couplingCost_eq_toReal (c : α → β → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (hcm : Measurable fun z : α × β => c z.1 z.2) (π : ProbabilityMeasure (α × β)) :
    couplingCost c π = (couplingCostENN c π).toReal := by
  rw [couplingCost,
    integral_eq_lintegral_of_nonneg_ae (f := fun z : α × β => c z.1 z.2)
      (Filter.Eventually.of_forall fun z => hc _ _) hcm.aestronglyMeasurable]
  rfl

/-- Converse of `integrable_of_couplingCostENN_ne_top`. -/
theorem couplingCostENN_ne_top_of_integrable (c : α → β → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (π : ProbabilityMeasure (α × β))
    (h : Integrable (fun z : α × β => c z.1 z.2) (π : Measure (α × β))) :
    couplingCostENN c π ≠ ⊤ := by
  have hfi := h.hasFiniteIntegral
  rw [HasFiniteIntegral] at hfi
  have hcongr : ∫⁻ z : α × β, ‖c z.1 z.2‖ₑ ∂(π : Measure (α × β)) = couplingCostENN c π :=
    lintegral_congr fun z => by rw [Real.enorm_eq_ofReal (hc _ _)]
  rw [hcongr] at hfi
  exact hfi.ne

/-! ## The Sinkhorn ball yields near-optimal, finite-entropy plans

The entropic analogue of `exists_coupling_couplingCost_lt`, and the reason
`Drsb.sdrsb_cost_bound` needs no edge at all. -/

/-- A finite Sinkhorn objective has finite cost summand. -/
theorem couplingCostENN_ne_top_of_sinkhornObjectiveENN_ne_top {c : α → β → ℝ} {κ : ℝ}
    {μhat : ProbabilityMeasure α} {νref : ProbabilityMeasure β} {γ : ProbabilityMeasure (α × β)}
    (h : sinkhornObjectiveENN c κ μhat νref γ ≠ ⊤) : couplingCostENN c γ ≠ ⊤ := by
  intro hc; rw [sinkhornObjectiveENN, hc] at h; simp at h

/-- A finite Sinkhorn objective has finite entropy summand. -/
theorem klDivMul_ne_top_of_sinkhornObjectiveENN_ne_top {c : α → β → ℝ} {κ : ℝ}
    {μhat : ProbabilityMeasure α} {νref : ProbabilityMeasure β} {γ : ProbabilityMeasure (α × β)}
    (h : sinkhornObjectiveENN c κ μhat νref γ ≠ ⊤) :
    ENNReal.ofReal κ *
      InformationTheory.klDiv (γ : Measure (α × β)) (prodMeasure μhat νref) ≠ ⊤ := by
  intro hk; rw [sinkhornObjectiveENN, hk] at h; simp at h

/-- **A finite Sinkhorn objective forces finite relative entropy** — provided `0 < κ`. Without
`κ > 0` the product `κ · KL` is finite for the trivial reason `0 · ∞ = 0`, and the coupling may
still be singular. -/
theorem klDiv_ne_top_of_sinkhornObjectiveENN_ne_top {c : α → β → ℝ} {κ : ℝ} (hκ : 0 < κ)
    {μhat : ProbabilityMeasure α} {νref : ProbabilityMeasure β} {γ : ProbabilityMeasure (α × β)}
    (h : sinkhornObjectiveENN c κ μhat νref γ ≠ ⊤) :
    InformationTheory.klDiv (γ : Measure (α × β)) (prodMeasure μhat νref) ≠ ⊤ := by
  have hκ0 : ENNReal.ofReal κ ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hκ
  intro hk
  exact klDivMul_ne_top_of_sinkhornObjectiveENN_ne_top h (by rw [hk, ENNReal.mul_top hκ0])

/-- A finite Sinkhorn objective forces the coupling to be absolutely continuous against the
entropic reference `μ̂ ⊗ ν`. -/
theorem absolutelyContinuous_of_sinkhornObjectiveENN_ne_top {c : α → β → ℝ} {κ : ℝ} (hκ : 0 < κ)
    {μhat : ProbabilityMeasure α} {νref : ProbabilityMeasure β} {γ : ProbabilityMeasure (α × β)}
    (h : sinkhornObjectiveENN c κ μhat νref γ ≠ ⊤) :
    (γ : Measure (α × β)) ≪ prodMeasure μhat νref :=
  (InformationTheory.klDiv_ne_top_iff.mp (klDiv_ne_top_of_sinkhornObjectiveENN_ne_top hκ h)).1

/-- **On a finite objective the real and `ℝ≥0∞` Sinkhorn objectives agree**, the real one being
the `toReal` of the other. This is the bridge that lets the `ℝ≥0∞`-valued `Wkappa` control the
real-valued budget appearing in `IsSinkhornPlan.objective_le`. -/
theorem sinkhornObjective_eq_toReal_of_ne_top {c : α → β → ℝ} (hc : ∀ x y, 0 ≤ c x y)
    (hcm : Measurable fun z : α × β => c z.1 z.2) {κ : ℝ} (hκ : 0 ≤ κ)
    {μhat : ProbabilityMeasure α} {νref : ProbabilityMeasure β} {γ : ProbabilityMeasure (α × β)}
    (h : sinkhornObjectiveENN c κ μhat νref γ ≠ ⊤) :
    sinkhornObjective c κ μhat νref γ = (sinkhornObjectiveENN c κ μhat νref γ).toReal := by
  simp only [sinkhornObjective, sinkhornObjectiveENN, klReal]
  rw [ENNReal.toReal_add (couplingCostENN_ne_top_of_sinkhornObjectiveENN_ne_top h)
      (klDivMul_ne_top_of_sinkhornObjectiveENN_ne_top h),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ, couplingCost_eq_toReal c hc hcm]

/-- Membership in the Sinkhorn ball, as an `ℝ≥0∞` bound. -/
theorem Wkappa_le_ofReal_of_mem_sinkhornBall {c : α → β → ℝ} {p₀ : ProbabilityMeasure α} {ν μ : ProbabilityMeasure β}
    {κ ε : ℝ} (hμ : μ ∈ sinkhornBall c p₀ ν κ ε) : Wkappa c κ ν p₀ μ ≤ ENNReal.ofReal ε := by
  obtain ⟨hfin, hle⟩ := hμ
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hle

/-- A nonempty Sinkhorn ball has a nonnegative radius (`W_{κ,ν} ≥ 0` is carried by `ℝ≥0∞`). -/
theorem radius_nonneg_of_mem_sinkhornBall {c : α → β → ℝ} {p₀ : ProbabilityMeasure α} {ν μ : ProbabilityMeasure β}
    {κ ε : ℝ} (hμ : μ ∈ sinkhornBall c p₀ ν κ ε) : 0 ≤ ε :=
  le_trans ENNReal.toReal_nonneg hμ.2

/-- Extract a coupling strictly below a bound on the `ℝ≥0∞` Sinkhorn discrepancy. -/
theorem exists_coupling_sinkhornObjectiveENN_lt {c : α → β → ℝ} {p₀ : ProbabilityMeasure α} {ν μ : ProbabilityMeasure β}
    {κ : ℝ} {b : ℝ≥0∞} (h : Wkappa c κ ν p₀ μ < b) :
    ∃ γ ∈ couplings p₀ μ, sinkhornObjectiveENN c κ p₀ ν γ < b := by
  rw [Wkappa, iInf_lt_iff] at h
  obtain ⟨γ, hγlt⟩ := h
  rw [iInf_lt_iff] at hγlt
  obtain ⟨hγ, hobj⟩ := hγlt
  exact ⟨γ, hγ, hobj⟩

/-- A **Sinkhorn transport plan** from the nominal `p₀` to the source `μ`, of budget `b`, against
the external reference `νref`, under the transport cost `c`.

The canonical object the entropic DRO bound consumes. Bundling its properties into a named
structure (rather than an anonymous `∃ γ, _ ∧ _ ∧ …`) gives every consumer stable field names and
keeps the SDRSB proofs from depending on conjunct order.

`absolutelyContinuous` and `klDiv_ne_top` are *not* redundant decoration: `sinkhornObjective` is
real-valued, so on a singular `γ` its entropic term silently reads `0` (see
`klReal_eq_zero_of_not_absolutelyContinuous`).  These fields ensure that `objective_le` refers to
a finite entropic objective. `integrable_cost` is likewise a genuine field, and a load-bearing one: it is what lets a
consumer disintegrate the plan *without* assuming finite second moments. All four are produced
automatically by `exists_isSinkhornPlan_of_mem_sinkhornBall`. -/
structure IsSinkhornPlan (c : α → β → ℝ) (κ : ℝ) (p₀ : ProbabilityMeasure α) (νref μ : ProbabilityMeasure β) (b : ℝ)
    (γ : ProbabilityMeasure (α × β)) : Prop where
  /-- `γ` transports the nominal `p₀` (first marginal) to the source `μ` (second marginal). -/
  mem_couplings : γ ∈ couplings p₀ μ
  /-- `γ` is absolutely continuous against the entropic reference `p₀ ⊗ νref`. -/
  absolutelyContinuous : (γ : Measure (α × β)) ≪ prodMeasure p₀ νref
  /-- `γ` has finite relative entropy against `p₀ ⊗ νref`. -/
  klDiv_ne_top : InformationTheory.klDiv (γ : Measure (α × β)) (prodMeasure p₀ νref) ≠ ⊤
  /-- `γ` has integrable transport cost. -/
  integrable_cost : Integrable (fun z : α × β => c z.1 z.2) (γ : Measure (α × β))
  /-- `γ`'s Sinkhorn objective is within the budget. -/
  objective_le : sinkhornObjective c κ p₀ νref γ ≤ b

/-- The independent coupling has zero entropic term, so its Sinkhorn objective is its cost. -/
theorem sinkhornObjectiveENN_prodCoupling (c : α → β → ℝ) (κ : ℝ) (p₀ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    sinkhornObjectiveENN c κ p₀ ν (prodCoupling p₀ ν) = couplingCostENN c (prodCoupling p₀ ν) := by
  have hkl : InformationTheory.klDiv ((prodCoupling p₀ ν : Measure (α × β)))
      (prodMeasure p₀ ν) = 0 := InformationTheory.klDiv_self _
  rw [sinkhornObjectiveENN, hkl, mul_zero, add_zero]

/-- **A concrete member of the Sinkhorn ball.** The external reference `ν` lies in the ball
around `p₀` as soon as the radius covers the independent coupling's transport cost — the entropic
term of `p₀ ⊗ ν` against `p₀ ⊗ ν` being zero.

Because `sinkhornBall` requires `Wkappa ≠ ⊤`, this theorem also identifies a concrete
nonemptiness threshold.  Unlike a metric ball, an entropic ball need not contain its centre `p₀`,
since the diagonal coupling is generally singular against the product reference (cf.
`WangGaoXie2023.primal_feasible_radius_nonneg`). -/
theorem mem_sinkhornBall_reference (c : α → β → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (hcm : Measurable fun z : α × β => c z.1 z.2) (p₀ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) (κ ε : ℝ)
    (hint : Integrable (fun z : α × β => c z.1 z.2) ((prodCoupling p₀ ν : Measure (α × β))))
    (hε : couplingCost c (prodCoupling p₀ ν) ≤ ε) :
    ν ∈ sinkhornBall c p₀ ν κ ε := by
  have hcostfin : couplingCostENN c (prodCoupling p₀ ν) ≠ ⊤ :=
    couplingCostENN_ne_top_of_integrable c hc _ hint
  have hle : Wkappa c κ ν p₀ ν ≤ couplingCostENN c (prodCoupling p₀ ν) := by
    rw [Wkappa, ← sinkhornObjectiveENN_prodCoupling c κ p₀ ν]
    exact iInf₂_le (prodCoupling p₀ ν) (prodCoupling_mem_couplings p₀ ν)
  have hWfin : Wkappa c κ ν p₀ ν ≠ ⊤ := ne_top_of_le_ne_top hcostfin hle
  refine ⟨hWfin, ?_⟩
  calc (Wkappa c κ ν p₀ ν).toReal
      ≤ (couplingCostENN c (prodCoupling p₀ ν)).toReal := ENNReal.toReal_mono hcostfin hle
    _ = couplingCost c (prodCoupling p₀ ν) := (couplingCost_eq_toReal c hc hcm _).symm
    _ ≤ ε := hε

/-- **The Sinkhorn ball yields near-optimal plans.** If `μ` lies in the Sinkhorn ball of radius
`ε`, then for every `η > 0` there is a Sinkhorn transport plan from `p₀` to `μ` of budget `ε + η`.

Because `Wkappa` infimises an **`ℝ≥0∞`** objective, a singular or infinite-cost coupling scores
`⊤` and cannot approach a finite infimum. Consequently, every near-optimal coupling is finite in
both summands. That finiteness
is exactly `absolutelyContinuous`, `klDiv_ne_top` **and** `integrable_cost`. `0 < κ` is what
converts finiteness of `κ · KL` into finiteness of `KL`.

As always with an infimum, the budget is `ε + η` and never `ε`: attainment is not claimed and is not
needed (`Drsb.sdrsb_cost_bound` closes the gap by letting `η ↓ 0`). -/
theorem exists_isSinkhornPlan_of_mem_sinkhornBall (c : α → β → ℝ) (hc : ∀ x y, 0 ≤ c x y)
    (hcm : Measurable fun z : α × β => c z.1 z.2)
    (p₀ : ProbabilityMeasure α) (ν μ : ProbabilityMeasure β) (κ ε η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (hμ : μ ∈ sinkhornBall c p₀ ν κ ε) :
    ∃ γ : ProbabilityMeasure (α × β), IsSinkhornPlan c κ p₀ ν μ (ε + η) γ := by
  have hε : 0 ≤ ε := radius_nonneg_of_mem_sinkhornBall hμ
  have hlt : Wkappa c κ ν p₀ μ < ENNReal.ofReal (ε + η) :=
    lt_of_le_of_lt (Wkappa_le_ofReal_of_mem_sinkhornBall hμ)
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  obtain ⟨γ, hγ, hobj⟩ := exists_coupling_sinkhornObjectiveENN_lt hlt
  have hobjfin : sinkhornObjectiveENN c κ p₀ ν γ ≠ ⊤ := ne_top_of_lt hobj
  refine ⟨γ, ⟨hγ, absolutelyContinuous_of_sinkhornObjectiveENN_ne_top hκ hobjfin,
    klDiv_ne_top_of_sinkhornObjectiveENN_ne_top hκ hobjfin,
    integrable_of_couplingCostENN_ne_top c hc hcm γ
      (couplingCostENN_ne_top_of_sinkhornObjectiveENN_ne_top hobjfin), ?_⟩⟩
  rw [sinkhornObjective_eq_toReal_of_ne_top hc hcm hκ.le hobjfin]
  calc (sinkhornObjectiveENN c κ p₀ ν γ).toReal
      ≤ (ENNReal.ofReal (ε + η)).toReal := ENNReal.toReal_mono (by simp) hobj.le
    _ = ε + η := ENNReal.toReal_ofReal (by linarith)


/-! ## The quadratic specializations

Everything above is Kantorovich: two measurable spaces, a cost `α → β → ℝ`, no algebra.
What follows needs a single normed group, and is separated for that reason. -/

section Quadratic

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]
/-! ## Second moments ⟹ quadratic cost is integrable under every coupling -/

/-- Under any coupling of `μ` with `ν`, the first coordinate's square-norm is integrable
as soon as `μ` has a finite second moment. -/
theorem integrable_normSq_fst_of_mem_couplings
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)) (hπ : π ∈ couplings μ ν)
    (hμ2 : Integrable (fun x => ‖x‖ ^ 2) (μ : Measure X)) :
    Integrable (fun z : X × X => ‖z.1‖ ^ 2) (π : Measure (X × X)) := by
  have hfst : (μ : Measure X) = Measure.map Prod.fst (π : Measure (X × X)) := hπ.1.symm
  have hae : AEStronglyMeasurable (fun x : X => ‖x‖ ^ 2)
      (Measure.map Prod.fst (π : Measure (X × X))) := hfst ▸ hμ2.1
  exact (integrable_map_measure hae measurable_fst.aemeasurable).mp (hfst ▸ hμ2)

/-- Under any coupling of `μ` with `ν`, the second coordinate's square-norm is integrable
as soon as `ν` has a finite second moment. -/
theorem integrable_normSq_snd_of_mem_couplings
    (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)) (hπ : π ∈ couplings μ ν)
    (hν2 : Integrable (fun x => ‖x‖ ^ 2) (ν : Measure X)) :
    Integrable (fun z : X × X => ‖z.2‖ ^ 2) (π : Measure (X × X)) := by
  have hsnd : (ν : Measure X) = Measure.map Prod.snd (π : Measure (X × X)) := hπ.2.symm
  have hae : AEStronglyMeasurable (fun x : X => ‖x‖ ^ 2)
      (Measure.map Prod.snd (π : Measure (X × X))) := hsnd ▸ hν2.1
  exact (integrable_map_measure hae measurable_snd.aemeasurable).mp (hsnd ▸ hν2)

/-- **Finite second moments of the marginals ⟹ every coupling has integrable quadratic
cost.** Dominate `‖x − y‖² ≤ 2‖x‖² + 2‖y‖²` and read each square-norm off its marginal.

Thus the integrability of the quadratic cost follows from the marginal moment assumptions for any
witnessing coupling. -/
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

Conversely, an integrable-cost coupling to a nominal law with finite second moment implies a finite
second moment for `μ`. -/
theorem integrable_normSq_of_mem_couplings_of_integrable_cost [OpensMeasurableSpace X]
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

end Quadratic
end ForMathlib.OT
