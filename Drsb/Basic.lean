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
import ForMathlib.OptimalTransport.WeakDuality
import ForMathlib.MeasureTheory.KLChainRule
import BlanchetMurthy2019.Basic
import GaoKleywegt2023.Basic
import WangGaoXie2023.Basic
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

/-- **Finite second moment** of a distribution — `𝔼_μ‖x‖² < ∞`. The standing regularity
of the WDRSB card: it is what makes `W₂²` a genuine constraint rather than a vacuous one
(`ForMathlib.OptimalTransport.Coupling`), and it replaces the OT-attainment hypothesis
`wdrsb_cost_bound` used to carry. -/
abbrev HasSecondMoment (μ : ProbabilityMeasure X) : Prop :=
  Integrable (fun x => ‖x‖ ^ 2) (μ : Measure X)

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

What remains genuinely assumed is the `≥` direction's **worst-case-measure attainment**
(`hattain`, `hbddP`) — the T4 research seam — plus regularity. -/
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
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε ∧ r = expect μ V })
    (hattain : ∃ μ : ProbabilityMeasure X, μ ∈ GaoKleywegt2023.ambiguitySet sqCost p₀ ε ∧
        expect μ V = GaoKleywegt2023.dualValue sqCost V p₀ ε) :
    droValue (wassersteinBall p₀ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧
          v = lam * ε + expect p₀ (BlanchetMurthy2019.Lc sqCost V lam) } := by
  -- `hfeas`: the nominal lies in its own ball (diagonal coupling has zero cost)
  have hfeas : (GaoKleywegt2023.ambiguitySet sqCost p₀ ε).Nonempty :=
    ⟨p₀, ForMathlib.OT.mem_wassersteinBall_self p₀ ε hε.le⟩
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
    hΨμ hOT hbddP hattain
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

/-- **WDRSB cost bound** (the `wdrsb_cost_bound.yaml` claim `E_perturbed[V] ≤ E_wc[V]`):
for any source `μ` inside the Wasserstein-2 ball of radius `ε` around the nominal `p₀`,
the expected cost is bounded by the WDRO dual worst-case value.

**Proved, with no optimal-transport edge.** It composes
`ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost` (the per-coupling Lagrangian
kernel) with `sqCost`'s symmetry (so the kernel's dual integrand matches Blanchet–Murthy's
`Lc`) and a *near-optimal* transport plan.

An earlier version assumed an **OT-attainment edge** `hOT`: that `W₂²(μ,p₀) ≤ ε` is
witnessed by a coupling of cost `≤ ε` with integrable cost. That hypothesis is now
**deleted**, because both halves of it are theorems:

* *attainment is not needed.* `W₂²` is an `sInf`, so it yields a plan of cost `< ε + η`
  for each `η > 0`, never one of cost `≤ ε`. Running the Lagrangian bound at `ε + η` and
  letting `η ↓ 0` (`le_of_forall_pos_le_add`) gives the same conclusion. This is the
  honest form of the argument: the `≥`/attainment direction is the T4 research seam, and
  the card's `≤` direction never needed it.
* *integrability is not an assumption.* Finite second moments of the two marginals force
  **every** coupling's quadratic cost to be integrable
  (`ForMathlib.OT.integrable_normSq_sub_of_mem_couplings`, via `‖x−y‖² ≤ 2‖x‖²+2‖y‖²`).

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
    -- finite second moments (replaces the old OT-attainment edge):
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

/-- **The deleted OT edge was never weaker: `hOT` ⟹ the second-moment hypotheses.**

`wdrsb_cost_bound` used to assume `hOT` — an integrable-cost coupling of cost `≤ ε`
witnessing `W₂²(μ,p₀) ≤ ε`. This theorem re-derives the card bound *from that old
hypothesis set*, showing the rewrite strengthened nothing: given a nominal of finite second
moment (`hp2`, which any statement of the problem carries), `hOT` already entails `μ`'s
finite second moment, because a single integrable-cost plan transfers the moment across
(`ForMathlib.OT.integrable_normSq_of_mem_couplings_of_integrable_cost`).

So `{hOT, hp2} ⊢ {hμ2, hp2}`, while the converse fails: no moment condition can produce an
*attaining* plan. The new hypothesis set is therefore strictly weaker, and this theorem is
the machine-checked receipt. It is kept as a compatibility shim for any downstream caller
that still carries an OT edge. -/
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

/-- **The Sinkhorn disintegration witness** at budget `b`: the `W_{κ,ν}(p₀, μ)` transport
from the nominal `p₀` to the source `μ` is realized by a conditional family `P` (each
`P x ≪ ν`) whose `p₀`-mixture is `μ` (`expect μ V = ∫∫ V dP dp₀`), whose disintegrated
entropic budget `∫ (𝔼_{P_x}‖x−·‖² + κ·KL(P_x‖ν)) dp₀` is `≤ b`, and which carries the
standard Donsker–Varadhan / aggregate integrability.

This is the entropic counterpart of a transport plan. Naming it separates the *one*
remaining SDRSB edge from the regularity noise, and lets the budget `b` be a parameter —
which is what allows the bound below to consume a **near-optimal** witness (`b = ε + η`)
rather than an attained one (`b = ε`).

The conditions on the conditionals are `p₀`-**a.e.**, because `Measure.condKernel` — the only
thing that ever produces `P` — is determined only up to a `p₀`-null set. `IsProbabilityMeasure`
stays `∀ x` since `condKernel` is a Markov kernel on the nose.

This edge is **discharged** by `isSinkhornWitness_of_coupling` below: on a standard-Borel `X`
you hand over a *coupling* `γ`, not a conditional family, and `condKernel` + the KL chain rule
build the witness. What survives is regularity of `γ`. -/
def IsSinkhornWitness (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ : ℝ)
    (μ : ProbabilityMeasure X) (b : ℝ) : Prop :=
  ∃ P : X → Measure X,
    (∀ x, IsProbabilityMeasure (P x)) ∧
    (∀ᵐ x ∂(p₀ : Measure X), P x ≪ (ν : Measure X)) ∧
    expect μ V = (∫ x, (∫ y, V y ∂(P x)) ∂(p₀ : Measure X)) ∧
    (∫ x, ((∫ y, sqCost x y ∂(P x)) + κ * klReal (P x) (ν : Measure X))
        ∂(p₀ : Measure X)) ≤ b ∧
    (∀ᵐ x ∂(p₀ : Measure X), Integrable V (P x)) ∧
    (∀ᵐ x ∂(p₀ : Measure X), Integrable (fun y => sqCost x y) (P x)) ∧
    (∀ᵐ x ∂(p₀ : Measure X), Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x)) ∧
    (∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X)) ∧
    Integrable (fun x => ∫ y, V y ∂(P x)) (p₀ : Measure X) ∧
    Integrable (fun x => ∫ y, sqCost x y ∂(P x)) (p₀ : Measure X) ∧
    Integrable (fun x => klReal (P x) (ν : Measure X)) (p₀ : Measure X) ∧
    (∀ lam, 0 < lam → Integrable
        (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X))

/-- A witness for a tighter budget is a witness for a looser one. -/
theorem IsSinkhornWitness.mono {p₀ ν : ProbabilityMeasure X} {V : X → ℝ} {κ : ℝ}
    {μ : ProbabilityMeasure X} {b b' : ℝ} (h : IsSinkhornWitness p₀ ν V κ μ b) (hb : b ≤ b') :
    IsSinkhornWitness p₀ ν V κ μ b' := by
  obtain ⟨P, hP, hac, hVdis, hbudget, rest⟩ := h
  exact ⟨P, hP, hac, hVdis, hbudget.trans hb, rest⟩

/-- **The SDRSB disintegration edge, discharged.** On a standard-Borel `X` you do not have to
supply a conditional family at all: hand over a **coupling** `γ ∈ Π(p₀, μ)` of finite entropy
relative to `p₀ ⊗ ν`, and `Measure.condKernel` + the KL chain rule build the witness.

Everything the old edge asked you to assert about `P` is now derived:

* `P := γ.condKernel`, and `p₀ ⊗ₘ P = γ` because `γ.fst = p₀` (`γ` is a coupling);
* `expect μ V = ∫∫ V dP dp₀` because `γ.snd = μ` (`Measure.integral_compProd`);
* the disintegrated budget equals `sinkhornObjective κ p₀ ν γ`, by `integral_compProd` on the
  cost and `ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_integral` (the chain rule with
  `η := Kernel.const X ν`, whose `p₀`-marginal term vanishes) on the entropy;
* `P x ≪ ν` and `Integrable (llr (P x) ν) (P x)` hold `p₀`-**a.e.**, because a finite conditional
  KL has a.e. finite slices (`ae_klDiv_kernel_ne_top`) and `klDiv_ne_top_iff` splits each finite
  slice into exactly those two facts. This is why the kernel had to be weakened to a.e. first.
* `hI_kl` is `integrable_toReal_klDiv_kernel`, and the two slice-integrability facts are
  `Measure.integrable_compProd_iff`.

Residual hypotheses are regularity of `γ` and the log-partition conditions on `ν`/`V`, which
concern the dual and not the transport. The cost's integrability is free from second moments
(`ForMathlib.OT.integrable_normSq_sub_of_mem_couplings`), exactly as in `wdrsb_cost_bound`.

⚠️ `hac`/`hfin` are **not** implied by `Wkappa κ ν p₀ μ ≤ ε`. `klReal` is `toReal`, so a `γ` with
`klDiv γ (p₀⊗ν) = ⊤` contributes the junk value `0` to that infimum. Ball membership alone
therefore does not produce a finite-entropy coupling — see the note on `sinkhornBall` in
`STATUS.md`. -/
theorem isSinkhornWitness_of_coupling
    [StandardBorelSpace X] [Nonempty X] [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ ν μ : ProbabilityMeasure X) (V : X → ℝ) (κ b : ℝ)
    (γ : ProbabilityMeasure (X × X)) (hγ : γ ∈ couplings p₀ μ)
    (hac : (γ : Measure (X × X)) ≪ prodMeasure p₀ ν)
    (hfin : InformationTheory.klDiv (γ : Measure (X × X)) (prodMeasure p₀ ν) ≠ ⊤)
    (hbudget : sinkhornObjective κ p₀ ν γ ≤ b)
    (hV : Integrable V (μ : Measure X))
    (hp2 : HasSecondMoment p₀) (hμ2 : HasSecondMoment μ)
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X)) :
    IsSinkhornWitness p₀ ν V κ μ b := by
  classical
  have hfstγ : Measure.map Prod.fst (γ : Measure (X × X)) = (p₀ : Measure X) := hγ.1
  have hsndγ : Measure.map Prod.snd (γ : Measure (X × X)) = (μ : Measure X) := hγ.2
  -- the conditional family is the coupling's conditional kernel
  set P : ProbabilityTheory.Kernel X X := (γ : Measure (X × X)).condKernel with hPdef
  have hfst' : (γ : Measure (X × X)).fst = (p₀ : Measure X) := hfstγ
  have hdis : (p₀ : Measure X) ⊗ₘ P = (γ : Measure (X × X)) := by
    rw [← hfst']; exact (γ : Measure (X × X)).disintegrate P
  have href : (p₀ : Measure X) ⊗ₘ (ProbabilityTheory.Kernel.const X (ν : Measure X))
      = prodMeasure p₀ ν := Measure.compProd_const
  have hac' : (p₀ : Measure X) ⊗ₘ P
      ≪ (p₀ : Measure X) ⊗ₘ (ProbabilityTheory.Kernel.const X (ν : Measure X)) := by
    rw [hdis, href]; exact hac
  have hfin' : InformationTheory.klDiv ((p₀ : Measure X) ⊗ₘ P)
      ((p₀ : Measure X) ⊗ₘ (ProbabilityTheory.Kernel.const X (ν : Measure X))) ≠ ⊤ := by
    rw [hdis, href]; exact hfin
  -- a.e. slice facts: absolute continuity, finiteness, and hence integrable `llr`
  have hac_slice : ∀ᵐ x ∂(p₀ : Measure X), P x ≪ (ν : Measure X) := by
    have := Measure.absolutelyContinuous_compProd_right_iff.mp hac'
    simpa using this
  have hfin_slice : ∀ᵐ x ∂(p₀ : Measure X),
      InformationTheory.klDiv (P x) (ν : Measure X) ≠ ⊤ := by
    have := ForMathlib.MeasureTheory.ae_klDiv_kernel_ne_top (p₀ : Measure X) P
      (ProbabilityTheory.Kernel.const X (ν : Measure X)) hac' hfin'
    simpa using this
  have h_llr : ∀ᵐ x ∂(p₀ : Measure X),
      Integrable (MeasureTheory.llr (P x) (ν : Measure X)) (P x) := by
    filter_upwards [hfin_slice] with x hx
    exact (InformationTheory.klDiv_ne_top_iff.mp hx).2
  have hI_kl : Integrable (fun x => klReal (P x) (ν : Measure X)) (p₀ : Measure X) := by
    have := ForMathlib.MeasureTheory.integrable_toReal_klDiv_kernel (p₀ : Measure X) P
      (ProbabilityTheory.Kernel.const X (ν : Measure X)) hac' hfin'
    simpa [klReal] using this
  -- the entropy term disintegrates (KL chain rule, constant second kernel)
  have hKL : klReal (γ : Measure (X × X)) (prodMeasure p₀ ν)
      = ∫ x, klReal (P x) (ν : Measure X) ∂(p₀ : Measure X) := by
    have := ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_integral (p₀ : Measure X) P
      (ProbabilityTheory.Kernel.const X (ν : Measure X)) hac' hfin'
    rw [hdis, href] at this
    simpa [klReal] using this
  -- integrability of the two integrands against `γ`
  have hVae : AEStronglyMeasurable V (Measure.map Prod.snd (γ : Measure (X × X))) := hsndγ ▸ hV.1
  have hVγ : Integrable (fun z : X × X => V z.2) (γ : Measure (X × X)) :=
    (integrable_map_measure hVae measurable_snd.aemeasurable).mp (hsndγ ▸ hV)
  have hcγ : Integrable (fun z : X × X => sqCost z.1 z.2) (γ : Measure (X × X)) :=
    ForMathlib.OT.integrable_normSq_sub_of_mem_couplings p₀ μ γ hγ hp2 hμ2
  have hVcp : Integrable (fun z : X × X => V z.2) ((p₀ : Measure X) ⊗ₘ P) := by rw [hdis]; exact hVγ
  have hccp : Integrable (fun z : X × X => sqCost z.1 z.2) ((p₀ : Measure X) ⊗ₘ P) := by
    rw [hdis]; exact hcγ
  -- slice integrability and integrability of the inner integrals
  have hf_P : ∀ᵐ x ∂(p₀ : Measure X), Integrable V (P x) := by
    have := ((Measure.integrable_compProd_iff hVcp.aestronglyMeasurable).mp hVcp).1
    simpa using this
  have hc_P : ∀ᵐ x ∂(p₀ : Measure X), Integrable (fun y => sqCost x y) (P x) :=
    ((Measure.integrable_compProd_iff hccp.aestronglyMeasurable).mp hccp).1
  have hI_V : Integrable (fun x => ∫ y, V y ∂(P x)) (p₀ : Measure X) := by
    have h := hVcp
    rw [Measure.compProd] at h
    simpa using h.integral_compProd
  have hI_c : Integrable (fun x => ∫ y, sqCost x y ∂(P x)) (p₀ : Measure X) := by
    have h := hccp
    rw [Measure.compProd] at h
    simpa using h.integral_compProd
  -- the two disintegration identities
  have hVdis : expect μ V = ∫ x, (∫ y, V y ∂(P x)) ∂(p₀ : Measure X) := by
    have h1 : expect μ V = ∫ z : X × X, V z.2 ∂(γ : Measure (X × X)) := by
      rw [expect, ← hsndγ, integral_map measurable_snd.aemeasurable hVae]
    rw [h1, ← hdis, Measure.integral_compProd hVcp]
  have hcostdis : couplingCost2 γ = ∫ x, (∫ y, sqCost x y ∂(P x)) ∂(p₀ : Measure X) := by
    show ∫ z : X × X, sqCost z.1 z.2 ∂(γ : Measure (X × X)) = _
    rw [← hdis, Measure.integral_compProd hccp]
  -- the disintegrated budget IS the Sinkhorn objective
  have hbud : (∫ x, ((∫ y, sqCost x y ∂(P x)) + κ * klReal (P x) (ν : Measure X))
      ∂(p₀ : Measure X)) ≤ b := by
    rw [integral_add hI_c (hI_kl.const_mul κ), integral_const_mul, ← hcostdis, ← hKL]
    exact hbudget
  exact ⟨fun x => P x, fun x => inferInstance, hac_slice, hVdis, hbud, hf_P, hc_P, h_llr,
    h_exp, hI_V, hI_c, hI_kl, hI_lp⟩

/-- **SDRSB cost bound** (the `sdrsb_cost_bound.yaml` claim): any source inside the
Sinkhorn ball (external reference `ν`) has expected cost bounded by the Sinkhorn-DRO dual
worst-case value. **PROVED** — the `≤`/weak-duality direction, the entropic analogue of
`wdrsb_cost_bound`, composing the proved Sinkhorn weak-duality kernel
`WangGaoXie2023.sinkhorn_weak_duality_kernel` (the per-point Gibbs/DV bound integrated over
`p₀`) with a near-optimal budget and `le_csInf`.

The single remaining edge is `hSink` (cf. AGENTS.md §6; the audit fixed the ball to share
the external reference `ν` — `prose/sinkhorn-dro-duality.md`). It is now **strictly weaker
than before**: it asks only for a witness of budget `≤ ε + η` for each `η > 0`, i.e. a
*near-optimal* disintegration, where it used to demand one of budget `≤ ε` — an
**attained** optimum. As in `wdrsb_cost_bound`, `W_{κ,ν}` is an `sInf` and so supplies the
former but never the latter; the exact conclusion is recovered by letting `η ↓ 0`. All the
attainment content has therefore been removed from the SDRSB edge as well, leaving
disintegration + regularity.

**`0 < lam`** in the dual set (not `0 ≤ lam`): at `lam = 0` the Lean `logPartition`
degenerates to `0` (junk from `0/0`) rather than the paper's `λ↓0` ess-sup limit, so the
`λ=0` term is excluded (documented limitation — the ess-sup convention is unencoded). -/
theorem sdrsb_cost_bound (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ sinkhornBall p₀ ν κ ε)
    (hSink : ∀ η : ℝ, 0 < η → Wkappa κ ν p₀ μ ≤ ε →
      IsSinkhornWitness p₀ ν V κ μ (ε + η)) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
  rintro v ⟨lam, hlam, rfl⟩
  -- the entropic infimum is not attained either: beat the dual value by an arbitrary `δ > 0`
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  obtain ⟨P, hP, hac, hVdis, hbudget, hf_P, hc_P, h_llr, h_exp, hI_V, hI_c, hI_kl, hI_lp⟩ :=
    hSink (δ / lam) (div_pos hδ hlam) hμ
  have key := WangGaoXie2023.sinkhorn_weak_duality_kernel p₀ ν sqCost V κ lam hκ hlam P hP hac
    hf_P hc_P h_llr (h_exp lam hlam) hI_V hI_c hI_kl (hI_lp lam hlam)
  have hb := mul_le_mul_of_nonneg_left hbudget (le_of_lt hlam)
  rw [show lam * (ε + δ / lam) = lam * ε + δ by field_simp] at hb
  rw [hVdis]
  simp only [WangGaoXie2023.sinkhornDualObjective, expect]
  linarith [key, hb]

/-- **The SDRSB relaxation strengthened nothing either.** The old edge — an *attained*
disintegration of budget `≤ ε` — implies the new near-optimal one (`b = ε ≤ ε + η`), so
the card bound still follows from it. The machine-checked receipt that `sdrsb_cost_bound`'s
hypothesis was weakened, not traded. The converse fails: an `sInf` supplies no minimizer. -/
theorem sdrsb_cost_bound_of_attained_witness (p₀ ν : ProbabilityMeasure X) (V : X → ℝ)
    (κ ε : ℝ) (hκ : 0 < κ) (μ : ProbabilityMeasure X) (hμ : μ ∈ sinkhornBall p₀ ν κ ε)
    (hSink : Wkappa κ ν p₀ μ ≤ ε → IsSinkhornWitness p₀ ν V κ μ ε) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } :=
  sdrsb_cost_bound p₀ ν V κ ε hκ μ hμ
    fun η hη hW => (hSink hW).mono (by linarith)

/-- **SDRSB cost bound from transport plans alone** — the card claim with no conditional family
and no attainment anywhere. Composes `sdrsb_cost_bound` (near-optimal budget, `η ↓ 0`) with
`isSinkhornWitness_of_coupling` (disintegration + KL chain rule).

`hplan` is the entropic analogue of what `wdrsb_cost_bound` gets for free from `W₂²`'s `sInf`:
for every `η > 0` there is a coupling of `p₀` with `μ`, of finite entropy relative to `p₀ ⊗ ν`,
whose Sinkhorn objective is within `η` of the radius. It is **not** derivable from
`μ ∈ sinkhornBall p₀ ν κ ε` as `Wkappa` is currently defined, because `klReal` is `toReal` and so
scores an infinite-entropy coupling as `0`; the finite-entropy requirement is exactly what that
junk value hides. Fixing `Wkappa` to be `ℝ≥0∞`-valued would make `hplan` a theorem — recorded in
`STATUS.md` as the next definitional cleanup. -/
theorem sdrsb_cost_bound_of_plans
    [StandardBorelSpace X] [Nonempty X] [OpensMeasurableSpace X] [MeasurableSub₂ X]
    (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ) (hκ : 0 < κ)
    (μ : ProbabilityMeasure X) (hμ : μ ∈ sinkhornBall p₀ ν κ ε)
    (hV : Integrable V (μ : Measure X))
    (hp2 : HasSecondMoment p₀) (hμ2 : HasSecondMoment μ)
    (h_exp : ∀ lam, 0 < lam → ∀ x, Integrable
        (fun y => Real.exp ((V y - lam * sqCost x y) / (lam * κ))) (ν : Measure X))
    (hI_lp : ∀ lam, 0 < lam → Integrable
        (fun x => WangGaoXie2023.logPartition ν sqCost V κ lam x) (p₀ : Measure X))
    (hplan : ∀ η : ℝ, 0 < η → ∃ γ ∈ couplings p₀ μ,
        (γ : Measure (X × X)) ≪ prodMeasure p₀ ν ∧
        InformationTheory.klDiv (γ : Measure (X × X)) (prodMeasure p₀ ν) ≠ ⊤ ∧
        sinkhornObjective κ p₀ ν γ ≤ ε + η) :
    expect μ V
      ≤ sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } :=
  sdrsb_cost_bound p₀ ν V κ ε hκ μ hμ fun η hη _ => by
    obtain ⟨γ, hγ, hac, hfin, hb⟩ := hplan η hη
    exact isSinkhornWitness_of_coupling p₀ ν μ V κ (ε + η) γ hγ hac hfin hb hV hp2 hμ2 h_exp hI_lp

/-- **SDRSB strong duality** — the Sinkhorn-DRO worst-case value of `V` over the Sinkhorn
ball equals the Wang–Gao–Xie log-partition dual (`f := V`, cost `‖·‖²`). Completes the
SDRSB capstone: `le_antisymm` of `droValue ≤ dual` (each source's `sdrsb_cost_bound`,
`csSup_le`) and `dual ≤ droValue` (the attaining worst-case measure, `le_csSup`). Same
honest edges as `sdrsb_cost_bound`, now `∀ μ` (`hSinkAll`, near-optimal in the same
`ε + η` sense), plus the worst-case-measure attainment edge (`hattain`) and `hbddP`; dual
over `0 < lam`. -/
theorem sdrsb_strong_duality (p₀ ν : ProbabilityMeasure X) (V : X → ℝ) (κ ε : ℝ)
    (hκ : 0 < κ)
    (hSinkAll : ∀ μ : ProbabilityMeasure X, μ ∈ sinkhornBall p₀ ν κ ε →
      ∀ η : ℝ, 0 < η → Wkappa κ ν p₀ μ ≤ ε → IsSinkhornWitness p₀ ν V κ μ (ε + η))
    (hbddP : BddAbove { r : ℝ | ∃ μ : ProbabilityMeasure X,
        μ ∈ sinkhornBall p₀ ν κ ε ∧ r = expect μ V })
    (hattain : ∃ μ : ProbabilityMeasure X, μ ∈ sinkhornBall p₀ ν κ ε ∧
        expect μ V = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam }) :
    droValue (sinkhornBall p₀ ν κ ε) V
      = sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
          v = WangGaoXie2023.sinkhornDualObjective p₀ ν sqCost V κ ε lam } := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ?_ ?_
    · obtain ⟨μ, hμ, _⟩ := hattain; exact ⟨expect μ V, μ, hμ, rfl⟩
    · rintro a ⟨μ, hμ, rfl⟩
      exact sdrsb_cost_bound p₀ ν V κ ε hκ μ hμ (hSinkAll μ hμ)
  · obtain ⟨μ, hμ, hμeq⟩ := hattain
    rw [← hμeq]
    exact le_csSup hbddP ⟨μ, hμ, rfl⟩

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

end Drsb
