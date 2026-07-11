/-
# Drsb — capstone: the GaTech MAGNET evaluation-card claims, composed from published theory

**Anchor.** This capstone formalizes the theorem the GaTech DRSB **MAGNET evaluation
cards** rest on — `E_perturbed[V] ≤ E_worst-case[V]` — and discharges it from the
**published** DRO theorems it composes:

* the value function `V` and optimal control are `ChenGeorgiouPavon2021`;
* the WDRSB worst-case cost bound is `BlanchetMurthy2019` / `GaoKleywegt2023`
  (Wasserstein-DRO strong duality) specialized to `f := V`, cost `‖·‖²`;
* the SDRSB (Sinkhorn) bound is `WangGaoXie2023` (Sinkhorn-DRO log-partition dual).

The two `expect μ V ≤ …` theorems are exactly the `wdrsb_cost_bound.yaml` /
`sdrsb_cost_bound.yaml` card claims. The cards' empirical evaluation samples adversarial
perturbations and checks `measured cost ≤ bound`; these theorems certify that inequality.

> The GaTech team's own unpublished DRSB manuscript (internal labels "Eq. 47",
> "Algorithm 5", referenced only in code comments) is **not a source** for this
> formalization and carries **~0 weight**. We anchor solely on the card and on the
> published theorems above. Where a code label like "Eq. 47" is mentioned, it is only
> pointing at the *card's* bound formula, whose backing is Wang–Gao–Xie.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.Coupling
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.OptimalTransport.WeakDuality
import ForMathlib.MeasureTheory.KLChainRule
import BlanchetMurthy2019.Basic
import GaoKleywegt2023.Basic
import WangGaoXie2023.Basic
import ForMathlib.OptimalTransport.SinkhornValueFunction
import ChenGeorgiouPavon2021.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open scoped ProbabilityTheory
open ForMathlib.OT

namespace Drsb

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]

/-- The quadratic (Wasserstein-2) transport cost `c(x, y) = ‖x − y‖²` used by both
DRSB cards. -/
def sqCost (x y : X) : ℝ := ‖x - y‖ ^ 2

/-- **Finite second moment** of a distribution — `𝔼_μ‖x‖² < ∞`. This regularity makes the
quadratic coupling cost integrable and prevents the real-valued `W₂²` interface from admitting
nonintegrable-cost artifacts. -/
abbrev HasSecondMoment (μ : ProbabilityMeasure X) : Prop :=
  Integrable (fun x => ‖x‖ ^ 2) (μ : Measure X)

omit [MeasurableSpace X] in
theorem sqCost_nonneg (x y : X) : 0 ≤ sqCost x y := by
  simp only [sqCost]; positivity

theorem measurable_sqCost [OpensMeasurableSpace X] [MeasurableSub₂ X] :
    Measurable fun z : X × X => sqCost z.1 z.2 :=
  ((measurable_fst.sub measurable_snd).norm).pow_const 2

/-! ## The DRSB value function

The DRSB value function is the Chen–Georgiou–Pavon stochastic-optimal-control value
`V(x) = 𝔼[∫₀¹ ½‖u_t‖² dt + ρ·g(X₁) | X₀ = x]`, with optimal control `u* = −∇V`
(`ChenGeorgiouPavon2021.optimal_control_eq_neg_grad_value`). Here we take it as an
abstract `V : X → ℝ`; its provenance lives in `ChenGeorgiouPavon2021`. -/

/-! ## WDRSB worst-case cost bound  (card `wdrsb_cost_bound.yaml`) -/

/-- **WDRSB strong duality** — the Wasserstein-DRO worst-case value of the DRSB value
function `V` over the `W₂²`-ball equals the Blanchet–Murthy / Gao–Kleywegt univariate
dual, specialized to `f := V`, cost `c := ‖·‖²`. Discharged by
`BlanchetMurthy2019.wdro_strong_duality` (equivalently `GaoKleywegt2023.strong_duality_thm1`).

Two of `strong_duality_thm1`'s hypotheses are **discharged here rather than assumed**:

* `hfeas` (the ambiguity set is nonempty) — the diagonal coupling gives `W₂²(p₀,p₀) ≤ 0 ≤ ε`
  (`ForMathlib.OT.mem_wassersteinBall_self`);
* `hOT` (near-optimal integrable-cost plans exist) — from the `sInf` defining `otCost`
  together with the second-moment hypotheses, via
  `ForMathlib.OT.exists_coupling_couplingCost_lt` and
  `ForMathlib.OT.integrable_normSq_sub_of_mem_couplings`.

The theorem assumes the reverse inequality `hge` together with regularity. The `BddAbove`
condition for primal expectations follows from `hbdd` at `lam = 0`, because a bounded-above
objective has bounded-above expectations
(`ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range`). -/
theorem wdrsb_strong_duality [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ)
    (hV : Integrable V (p₀ : Measure X)) (hε : 0 < ε)
    (_hκ : GaoKleywegt2023.kappa sqCost V p₀ ≠ ⊤)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => V ξ - lam * sqCost ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun ζ => sSup (Set.range (fun ξ => V ξ - lam * sqCost ξ ζ))) (p₀ : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε →
        Integrable V (μ : Measure X))
    -- second moments: the nominal, and every source in the ambiguity set
    (hp2 : HasSecondMoment p₀)
    (hmom : ∀ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε →
        HasSecondMoment μ)
    -- reverse duality; optimizer attainment is sufficient but not required
    (hge : GaoKleywegt2023.dualValue sqCost V p₀ ε
        ≤ GaoKleywegt2023.primalValue sqCost V p₀ ε) :
    droValue (wassersteinBall p₀ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  -- `hfeas`: the nominal lies in its own ball (diagonal coupling has zero cost)
  have hfeas : (GaoKleywegt2023.ambiguitySet sqCost p₀ ε).Nonempty :=
    ⟨p₀, ForMathlib.OT.mem_wassersteinBall_self p₀ ε hε.le⟩
  -- `hbddP`: `hbdd` at `lam = 0` says `V` is bounded above, and a bounded objective has
  -- bounded expectations
  -- `hOT`: near-optimal plans exist, and second moments make their cost integrable
  have hOT : ∀ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε →
      ∀ η : ℝ, 0 < η →
      ∃ π : ProbabilityMeasure (X × X), π ∈ couplings μ p₀ ∧ couplingCost sqCost π ≤ ε + η ∧
        Integrable (fun z : X × X => sqCost z.1 z.2) (π : Measure (X × X)) := by
    intro μ hμ η hη
    obtain ⟨π, hπ, hlt⟩ := ForMathlib.OT.exists_coupling_couplingCost_lt sqCost μ p₀ (ε + η)
      (lt_of_le_of_lt hμ (by linarith))
    exact ⟨π, hπ, hlt.le,
      ForMathlib.OT.integrable_normSq_sub_of_mem_couplings μ p₀ π hπ (hmom μ hμ) hp2⟩
  -- `sqCost` is symmetric, so Blanchet–Murthy's `Lc` = −(Gao–Kleywegt's `Φ`) pointwise
  have hsymm : ∀ a b : X, sqCost a b = sqCost b a := by
    intro a b; simp only [sqCost]; rw [norm_sub_rev]
  have hLcPhi : ∀ (lam : ℝ) (x : X),
      BlanchetMurthy2019.Lc sqCost V lam x = -(GaoKleywegt2023.Phi sqCost V lam x) := by
    intro lam x
    rw [BlanchetMurthy2019.Lc, GaoKleywegt2023.Phi, ← Real.sSup_neg]
    congr 1
    rw [← Set.image_neg_eq_neg, ← Set.range_comp]
    congr 1; funext ξ; simp only [Function.comp_apply]; rw [hsymm x ξ]; ring
  have hexpLc : ∀ lam : ℝ, expect p₀ (BlanchetMurthy2019.Lc sqCost V lam)
      = - expect p₀ (fun ζ => GaoKleywegt2023.Phi sqCost V lam ζ) := by
    intro lam
    unfold expect
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ζ => hLcPhi lam ζ))
  -- apply the proved general strong duality (specialized to `sqCost, V, p₀, ε`)
  have hsd := GaoKleywegt2023.strong_duality_thm1 sqCost V p₀ ε hV hε _hκ hfeas hbdd hφint
    hΨμ hOT hge
  rw [show droValue (wassersteinBall p₀ ε) V = GaoKleywegt2023.primalValue sqCost V p₀ ε from rfl,
    hsd, GaoKleywegt2023.dualValue]
  -- the two dual sets coincide (Φ-form = Lc-form)
  congr 1
  ext v
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨lam, hlam, by rw [hexpLc lam]; ring⟩
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨lam, hlam, by rw [hexpLc lam]; ring⟩


/-- **WDRSB strong duality from explicit regularity assumptions.** The reverse inequality is
provided by `GaoKleywegt2023.dualValue_le_primalValue`, proved from the converse Lagrangian bound,
an optimal multiplier, and concavity of the DRO value function.

What remains are checkable regularity conditions on the value function `V` and the quadratic cost:
continuity, boundedness, the conjugate's finiteness, integrability, and a zero-cost feasible plan
(which the diagonal coupling supplies, `sqCost x x = 0`). -/
theorem wdrsb_strong_duality_of_regularity
    [SecondCountableTopology X] [Nonempty X] [BorelSpace X] [MeasurableSub₂ X]
    (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ)
    (hV : Integrable V (p₀ : Measure X)) (hε : 0 < ε)
    (_hκ : GaoKleywegt2023.kappa sqCost V p₀ ≠ ⊤)
    (hVc : Continuous V) (hcc : Continuous fun z : X × X => sqCost z.1 z.2)
    (C : ℝ) (hVb : ∀ x, |V x| ≤ C)
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ ζ : X,
        BddAbove (Set.range (fun ξ => V ξ - lam * sqCost ξ ζ)))
    (hφint : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (fun ζ => sSup (Set.range (fun ξ => V ξ - lam * sqCost ξ ζ))) (p₀ : Measure X))
    (hΨμ : ∀ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε →
        Integrable V (μ : Measure X))
    (hp2 : HasSecondMoment p₀)
    (hmom : ∀ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε →
        HasSecondMoment μ)
    (hne0 : (ForMathlib.OT.droValueSet sqCost V p₀ 0).Nonempty) :
    droValue (wassersteinBall p₀ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } :=
  wdrsb_strong_duality p₀ V ε hV hε _hκ hbdd hφint hΨμ hp2 hmom
    (GaoKleywegt2023.dualValue_le_primalValue sqCost V p₀ ε hε hVc hcc sqCost_nonneg C hVb
      hbdd hφint hΨμ hne0)

/-- **WDRSB cost bound** (the `wdrsb_cost_bound.yaml` claim `E_perturbed[V] ≤ E_wc[V]`):
for any source `μ` inside the Wasserstein-2 ball of radius `ε` around the nominal `p₀`,
the expected cost is bounded by the WDRO dual worst-case value.

The proof composes
`ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost` (the per-coupling Lagrangian
kernel) with `sqCost`'s symmetry (so the kernel's dual integrand matches Blanchet–Murthy's
`Lc`) and a *near-optimal* transport plan.

Because `W₂²` is an `sInf`, ball membership yields a coupling of cost `< ε + η` for each
`η > 0`; applying the Lagrangian bound at `ε + η` and letting `η ↓ 0` proves the result without
optimal-plan attainment. Finite second moments of the marginals make every coupling's quadratic
cost integrable (`ForMathlib.OT.integrable_normSq_sub_of_mem_couplings`, via
`‖x−y‖² ≤ 2‖x‖²+2‖y‖²`).

The surviving hypotheses are all checkable regularity: `hV`/`hbdd`/`hLc` make the three
expectations well defined, and `hμ2`/`hp2` are the finite second moments. The latter are
not cosmetic. `couplingCost` is a *Bochner* integral, so it returns the junk value `0` on a
coupling whose cost is not integrable. Hence if `p₀` has a finite second moment but `μ`
does not, then no coupling of the two has integrable cost
(`ForMathlib.OT.integrable_normSq_of_mem_couplings_of_integrable_cost`, contrapositive),
every coupling contributes `0` to the infimum, and `W₂²(μ,p₀) = 0 ≤ ε`: such a `μ` sits in
`wassersteinBall p₀ ε` for **every** radius `ε`, so its ball membership constrains nothing
and supplies no integrable-cost plan for the Lagrangian bound to run on. `hμ2` is exactly
what excludes that degenerate membership. -/
theorem wdrsb_cost_bound [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ wassersteinBall p₀ ε)
    -- regularity (integrability / sup-boundedness):
    (hV : Integrable V (μ : Measure X))
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ y : X,
        BddAbove (Set.range (fun x => V x - lam * sqCost x y)))
    (hLc : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (BlanchetMurthy2019.Lc sqCost V lam) (p₀ : Measure X))
    -- finite second moments, used to obtain integrable near-optimal couplings:
    (hμ2 : HasSecondMoment μ) (hp2 : HasSecondMoment p₀) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  -- sqCost is symmetric, so Blanchet–Murthy's `Lc` IS the kernel's dual integrand
  have hsymm : ∀ x y : X, sqCost x y = sqCost y x := by
    intro x y; simp only [sqCost]; rw [norm_sub_rev]
  have hLc_eq : ∀ lam : ℝ, BlanchetMurthy2019.Lc sqCost V lam
      = fun y => sSup (Set.range (fun x => V x - lam * sqCost x y)) := by
    intro lam; funext a
    have h : (fun y => V y - lam * sqCost a y) = (fun x => V x - lam * sqCost x a) := by
      funext t; rw [hsymm a t]
    show sSup (Set.range (fun y => V y - lam * sqCost a y))
        = sSup (Set.range (fun x => V x - lam * sqCost x a))
    rw [h]
  -- `expect μ V` is a lower bound of the dual set
  refine le_csInf ⟨_, 0, le_rfl, rfl⟩ ?_
  rintro v ⟨lam, hlam, rfl⟩
  have hφ : Integrable (fun y => sSup (Set.range (fun x => V x - lam * sqCost x y)))
      (p₀ : Measure X) := by rw [← hLc_eq lam]; exact hLc lam hlam
  -- it suffices to beat the dual value by an arbitrary `δ > 0`; the OT infimum is not attained
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  have hlam1 : (0 : ℝ) < lam + 1 := by linarith
  set η : ℝ := δ / (lam + 1) with hηdef
  have hη : 0 < η := div_pos hδ hlam1
  -- `W₂²(μ, p₀) ≤ ε < ε + η`, so *some* coupling has cost `< ε + η` (no attainment needed)
  obtain ⟨π, hπ, hcost_lt⟩ := ForMathlib.OT.exists_coupling_couplingCost_lt sqCost μ p₀ (ε + η)
    (lt_of_le_of_lt hμ (by linarith))
  -- second moments ⟹ that plan's cost is integrable (no hypothesis needed)
  have hcost_int : Integrable (fun z : X × X => sqCost z.1 z.2) (π : Measure (X × X)) :=
    ForMathlib.OT.integrable_normSq_sub_of_mem_couplings μ p₀ π hπ hμ2 hp2
  have key := ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost
    sqCost V lam hlam μ p₀ π hπ (hbdd lam hlam) hV hφ hcost_int
  rw [← hLc_eq lam] at key
  have hstep : lam * couplingCost sqCost π ≤ lam * (ε + η) :=
    mul_le_mul_of_nonneg_left hcost_lt.le hlam
  have hηbd : lam * η ≤ δ := by
    rw [hηdef, mul_div_assoc', div_le_iff₀ hlam1]; nlinarith
  nlinarith [key, hstep, hηbd]

/-- **Compatibility form using an explicit transport witness.** An integrable-cost coupling
of cost `≤ ε`, together with a finite second moment for the nominal law, transfers the second
moment to `μ` via
`ForMathlib.OT.integrable_normSq_of_mem_couplings_of_integrable_cost`. The main
`wdrsb_cost_bound` can then be applied. -/
theorem wdrsb_cost_bound_of_ot_edge [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ : ProbabilityMeasure X) (V : X → ℝ) (ε : ℝ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ wassersteinBall p₀ ε)
    (hV : Integrable V (μ : Measure X))
    (hbdd : ∀ lam : ℝ, 0 ≤ lam → ∀ y : X,
        BddAbove (Set.range (fun x => V x - lam * sqCost x y)))
    (hLc : ∀ lam : ℝ, 0 ≤ lam →
        Integrable (BlanchetMurthy2019.Lc sqCost V lam) (p₀ : Measure X))
    (hp2 : HasSecondMoment p₀)
    (hOT : W2sq μ p₀ ≤ ε →
        ∃ π ∈ couplings μ p₀, couplingCost sqCost π ≤ ε ∧
          Integrable (fun z : X × X => sqCost z.1 z.2) (π : Measure (X × X))) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  obtain ⟨π, hπ, _, hcost_int⟩ := hOT hμ
  exact wdrsb_cost_bound p₀ V ε μ hμ hV hbdd hLc
    (ForMathlib.OT.integrable_normSq_of_mem_couplings_of_integrable_cost μ p₀ π hπ hcost_int hp2)
    hp2

/-! ## SDRSB worst-case cost bound  (card `sdrsb_cost_bound.yaml`) -/

/-! ## The SDRSB disintegration

The general (cost- and objective-parametrized) machinery lives in `WangGaoXie2023`, next to the
`logPartition` it consumes. `Drsb` specializes at `c := sqCost`, `f := V`. -/

/-- The SDRSB Sinkhorn disintegration: `WangGaoXie2023.HasSinkhornDisintegration` at the quadratic
cost and the DRSB value function. -/
abbrev HasSinkhornDisintegration (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ : ℝ)
    (μ : ProbabilityMeasure X) (b : ℝ) : Prop :=
  WangGaoXie2023.HasSinkhornDisintegration sqCost p₀ ν V κ μ b

/-- **SDRSB weak duality, given near-optimal witnesses.** The kernel of the card bound: if for
every `η > 0` the source `μ` admits a Sinkhorn disintegration witness of budget `≤ ε + η`, then
its expected cost is bounded by the Sinkhorn-DRO dual value.

Composes `WangGaoXie2023.sinkhorn_weak_duality_kernel` (the per-point Gibbs/Donsker–Varadhan
bound integrated over `p₀`) with `le_csInf` and a limit `η ↓ 0`. The infimum defining
`W_{κ,ν}` supplies the required near-optimal witnesses without an attainment assumption.

Callers should prefer `sdrsb_cost_bound`, which *builds* the disintegrations. -/
theorem sdrsb_cost_bound_of_disintegrations (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ)
    (hκ : 0 < κ) (μ : ProbabilityMeasure X)
    (hSink : ∀ η : ℝ, 0 < η → HasSinkhornDisintegration p₀ ν V κ μ (ε + η)) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
  rintro v ⟨lam, hlam, rfl⟩
  -- the entropic infimum is not attained: beat the dual value by an arbitrary `δ > 0`
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  obtain ⟨P, hd⟩ := hSink (δ / lam) (div_pos hδ hlam)
  have key := WangGaoXie2023.sinkhorn_weak_duality_kernel p₀ ν sqCost V κ lam hκ hlam P
    hd.isProbabilityMeasure hd.absolutelyContinuous hd.integrable_V hd.integrable_cost
    hd.integrable_llr (hd.integrable_exp lam hlam) hd.integrable_integral_V
    hd.integrable_integral_cost hd.integrable_klReal (hd.integrable_logPartition lam hlam)
  have hb := mul_le_mul_of_nonneg_left hd.budget_le (le_of_lt hlam)
  rw [show lam * (ε + δ / lam) = lam * ε + δ by field_simp] at hb
  rw [hd.expect_eq]
  simp only [WangGaoXie2023.sinkhornDualObjective, expect]
  linarith [key, hb]

/-- **SDRSB cost bound** (the `sdrsb_cost_bound.yaml` claim `E_perturbed[V] ≤ E_wc[V]`): any
source `μ` inside the Sinkhorn ball around the nominal `p₀` (external reference `ν`) has
expected cost bounded by the Sinkhorn-DRO dual worst-case value.

This is the entropic counterpart of `wdrsb_cost_bound`. Ball membership provides the required
transport and disintegration data:

* `ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall` extracts, for each `η > 0`, a plan
  `γ ∈ Π(p₀, μ)` of finite entropy relative to `p₀ ⊗ ν` and Sinkhorn objective `≤ ε + η`. This
  is a theorem because `Wkappa` infimises the **`ℝ≥0∞`** objective, in which a singular coupling
  correctly scores `⊤` instead of the junk value `0`;
* `hasSinkhornDisintegration_of_isSinkhornPlan` turns that plan into a conditional family, via
  `Measure.condKernel` and the KL chain rule;
* `sdrsb_cost_bound_of_disintegrations` runs the Donsker–Varadhan bound and lets `η ↓ 0`.

The surviving hypotheses are checkable regularity: `hV`, and `h_exp`/`hI_lp`, which constrain the
*dual* — the log-partition of `V` against `ν` — and say nothing about transport. **No second
moments**: the plan's cost-integrability is a *field* of `IsSinkhornPlan`, derived from the
finiteness of its `ℝ≥0∞` cost. (Contrast `wdrsb_cost_bound`, whose `otCost` is still real-valued
and so must exclude infinite-second-moment junk by hypothesis.)

**`0 < lam`** in the dual set (not `0 ≤ lam`): at `lam = 0` the Lean `logPartition` degenerates
to `0` (junk from `0/0`) rather than the paper's `λ↓0` ess-sup limit, so the `λ=0` term is
excluded (documented limitation — the ess-sup convention is unencoded). -/
theorem sdrsb_cost_bound
    [StandardBorelSpace X] [Nonempty X] [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ sinkhornBall sqCost p₀ ν κ ε)
    (hV : Integrable V (μ : Measure X))
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X)) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } :=
  sdrsb_cost_bound_of_disintegrations p₀ ν V κ ε hκ μ fun η hη => by
    obtain ⟨γ, hplan⟩ := ForMathlib.OT.exists_isSinkhornPlan_of_mem_sinkhornBall
      sqCost sqCost_nonneg measurable_sqCost p₀ ν μ κ ε η hκ hη hμ
    exact WangGaoXie2023.hasSinkhornDisintegration_of_isSinkhornPlan hplan V hV h_exp hI_lp

/-- **Compatibility form using an attained disintegration.** A disintegration with budget
`≤ ε` is also a valid near-optimal witness for every budget `ε + η`, so it implies the general
SDRSB cost bound. -/
theorem sdrsb_cost_bound_of_attained_disintegration (p₀ ν : ProbabilityMeasure X) (V : X → ℝ)
    (κ ε : ℝ) (hκ : 0 < κ) (μ : ProbabilityMeasure X)
    (hSink : HasSinkhornDisintegration p₀ ν V κ μ ε) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } :=
  sdrsb_cost_bound_of_disintegrations p₀ ν V κ ε hκ μ fun η hη => hSink.mono (by linarith)

/-- **SDRSB strong duality** — the Sinkhorn-DRO worst-case value of `V` over the Sinkhorn ball
equals the Wang–Gao–Xie log-partition dual (`f := V`, cost `‖·‖²`). The forward inequality is
obtained by applying `sdrsb_cost_bound` to each feasible source; the reverse inequality uses
`WangGaoXie2023.sinkhornDual_le_droValue` under a strict-feasibility hypothesis.

The regularity assumptions are quantified over every source in the ball. The `BddAbove` gate is
derived from `hVbdd`. The dual ranges over `0 < lam`; the `lam = 0` essential-supremum endpoint is
not part of this specialization. -/
theorem sdrsb_strong_duality
    [StandardBorelSpace X] [Nonempty X] [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ) (hVm : Measurable V)
    (hV : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall sqCost p₀ ν κ ε → Integrable V (μ : Measure X))
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X))
    (hV_P : ∀ lam : ℝ, 0 < lam → ∀ x, Integrable V
      ((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ)))
    (hc_P : ∀ lam : ℝ, 0 < lam → ∀ x, Integrable (fun y => sqCost x y)
      ((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ)))
    (hV_norm : ∀ lam : ℝ, 0 < lam → Integrable (fun x => ∫ y, ‖V y‖
      ∂((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ))) (p₀ : Measure X))
    (hc_norm : ∀ lam : ℝ, 0 < lam → Integrable (fun x => ∫ y, ‖sqCost x y‖
      ∂((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ))) (p₀ : Measure X))
    (hklint : ∀ lam : ℝ, 0 < lam → Integrable (fun x => klReal
      ((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ)) (ν : Measure X))
      (p₀ : Measure X))
    (hVbdd : BddAbove (Set.range V))
    (hfeas : (sinkhornBall sqCost p₀ ν κ ε).Nonempty)
    -- **Slater**: some coupling is strictly feasible, placing `ε` in the interior of the
    -- entropic value function's domain.
    {t₀ : ℝ} (ht₀ : t₀ ∈ ForMathlib.OT.sinkhornDomain sqCost V κ p₀ ν) (ht₀ε : t₀ < ε) :
    droValue (sinkhornBall sqCost p₀ ν κ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  obtain ⟨C, hC⟩ := hVbdd
  have hVb : ∀ x, V x ≤ C := fun x => hC ⟨x, rfl⟩
  -- the `BddAbove` gate is a consequence of `V` being bounded above
  have hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
      μ ∈ sinkhornBall sqCost p₀ ν κ ε ∧ r = expect μ V } :=
    ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range _ V ⟨C, hC⟩ hV
  refine le_antisymm ?_ ?_
  · refine csSup_le ?_ ?_
    · obtain ⟨μ, hμ⟩ := hfeas; exact ⟨expect μ V, μ, hμ, rfl⟩
    · rintro a ⟨μ, hμ, rfl⟩
      exact sdrsb_cost_bound p₀ ν V κ ε hκ μ hμ (hV μ hμ) h_exp hI_lp
  · exact WangGaoXie2023.sinkhornDual_le_droValue p₀ ν sqCost V κ ε hκ sqCost_nonneg
      measurable_sqCost hVm C hVb hV h_exp hI_lp hV_P hc_P hV_norm hc_norm hklint hfeas ht₀ ht₀ε

/-- **SDRSB terminal-cost bound** — the closed form the `sdrsb_cost_bound.yaml` card's
measurement compares against: the worst-case cost minus a log-partition term over the
terminal reference `ν`,
`Bound = E_wc[V] − ρ · log 𝔼_ν[e^{g(X₁)}]`.

This is the `WangGaoXie2023.logPartition` term (published Wang–Gao–Xie Sinkhorn-DRO dual)
with `f := ρ·g`, `c := 0` at the terminal layer — the mathematical backing of the bound.
(The GaTech code labels this term "Eq. 47" internally; that label has no published or
normative status and is not a source here — see the module header.) -/
noncomputable def sdrsbTerminalBound (ν : ProbabilityMeasure X) (g : X → ℝ) (ρ Ewc : ℝ) : ℝ :=
  Ewc - ρ * Real.log (∫ x, Real.exp (g x) ∂(ν : Measure X))


/-- **SDRSB strong duality, with Slater discharged to a checkable inequality.**

The strict-feasibility hypothesis of `sdrsb_strong_duality` holds as soon as the radius `ε`
exceeds the transport cost of the independent coupling `p₀ ⊗ ν`, whose entropic term vanishes.
This reduces Slater's condition to a concrete scalar inequality. -/
theorem sdrsb_strong_duality_of_radius_gt_independent_cost
    [StandardBorelSpace X] [Nonempty X] [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ) (hVm : Measurable V)
    (hV : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall sqCost p₀ ν κ ε → Integrable V (μ : Measure X))
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X))
    (hV_P : ∀ lam : ℝ, 0 < lam → ∀ x, Integrable V
      ((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ)))
    (hc_P : ∀ lam : ℝ, 0 < lam → ∀ x, Integrable (fun y => sqCost x y)
      ((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ)))
    (hV_norm : ∀ lam : ℝ, 0 < lam → Integrable (fun x => ∫ y, ‖V y‖
      ∂((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ))) (p₀ : Measure X))
    (hc_norm : ∀ lam : ℝ, 0 < lam → Integrable (fun x => ∫ y, ‖sqCost x y‖
      ∂((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ))) (p₀ : Measure X))
    (hklint : ∀ lam : ℝ, 0 < lam → Integrable (fun x => klReal
      ((ν : Measure X).tilted fun y => (V y - lam * sqCost x y) / (lam * κ)) (ν : Measure X))
      (p₀ : Measure X))
    (hVbdd : BddAbove (Set.range V))
    (hfeas : (sinkhornBall sqCost p₀ ν κ ε).Nonempty)
    (hVν : Integrable V (ν : Measure X))
    (hcprod : Integrable (fun z : X × X => sqCost z.1 z.2) (ForMathlib.OT.prodMeasure p₀ ν))
    -- **Slater, concretely**: the radius beats the independent coupling's transport cost.
    (hεgt : couplingCost sqCost (ForMathlib.OT.prodCoupling p₀ ν) < ε) :
    droValue (sinkhornBall sqCost p₀ ν κ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  obtain ⟨t₀, ht₀, ht₀ε⟩ := ForMathlib.OT.exists_slater_of_couplingCost_prodCoupling_lt
    sqCost V κ p₀ ν hVν hcprod hεgt
  exact sdrsb_strong_duality p₀ ν V κ ε hκ hVm hV h_exp hI_lp hV_P hc_P hV_norm hc_norm hklint
    hVbdd hfeas ht₀ ht₀ε

end Drsb
