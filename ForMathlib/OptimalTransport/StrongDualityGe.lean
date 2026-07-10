/-
# The duality gap is zero: the `≥` half of Wasserstein-DRO strong duality

**`hge`, proved.** For a continuous bounded reward `f`, a continuous nonnegative cost `c`, a
separable Borel sample space, a strictly positive radius `δ`, and a zero-cost feasible plan,

`inf_{λ > 0} ( λδ + 𝔼_ν[φ_λ] )  ≤  sup { 𝔼_μ[f] : T_c(μ, ν) ≤ δ }`,  `φ_λ(y) = sup_x (f x − λ c(x,y))`.

Combined with the always-true `≤` half (`ForMathlib.OT.expect_le_dualIntegrand_add_lam_couplingCost`,
assembled in `GaoKleywegt2023.weak_duality_prop1`), this is Blanchet–Murthy Thm 1 / Gao–Kleywegt
Thm 1 — the theorem the four DRSB strong-duality capstones had been carrying as the hypothesis
`hge`.

## The three ingredients

1. `ForMathlib.OT.exists_coupling_lagrangian_ge` — the **converse Lagrangian bound**: `𝔼_ν[φ_λ]` is
   achieved, to within `ε`, by pushing `ν` forward along a measurable near-maximizer of the
   `c`-transform. The selector comes from `ForMathlib.MeasureTheory.exists_measurable_eps_argmax_of_separable`,
   which needs **no Kuratowski–Ryll-Nardzewski**: a continuous integrand on a separable domain
   attains its supremum to within `ε` on a countable dense set, and `Nat.find` on an enumeration is
   measurable.
2. `ForMathlib.Analysis.exists_nonneg_multiplier'` — the **optimal multiplier**: a nondecreasing
   concave function on a convex subset of `ℝ` has a nonnegative supergradient `λ*` at an interior
   point, giving `h t + λ*·(δ − t) ≤ h δ`. (Mathlib has `ConcaveOn` and slope lemmas but no
   sub/supergradient existence at all.)
3. `ForMathlib.OT.concaveOn_droValueAt` — the **DRO value function is concave and nondecreasing**,
   because the coupling set is convex (`mix_mem_couplings`) and cost/reward are affine on it.

## The assembly

Run (1) at `λ = λ* + η` for a small `η > 0` — never at `λ*` itself, so that `λ > 0` is available for
the cost-integrability step, and so that the `λ* = 0` case needs no separate treatment. Writing
`t = 𝔼_π[c] ≥ 0` for the near-optimal plan's cost:

`λδ + 𝔼_ν[φ_λ] ≤ 𝔼_μ[f] + λ(δ − t) + ε/2`  (by (1))
`             = 𝔼_μ[f] + λ*(δ − t) + η(δ − t) + ε/2`
`             ≤ h δ + ηδ + ε/2`             (by (2) and `𝔼_μ[f] ≤ h t`, using `t ≥ 0`)
`             ≤ h δ + ε`                    (choosing `η ≤ ε/(2δ)`).

The dual set is bounded below by `𝔼_{μ₀}[f]` for the zero-cost feasible plan, via the *forward*
Lagrangian bound — which is what makes `csInf_le` applicable.
-/
import Mathlib
import ForMathlib.OptimalTransport.Basic
import ForMathlib.OptimalTransport.WeakDuality
import ForMathlib.OptimalTransport.DroValue
import ForMathlib.OptimalTransport.ConverseLagrangian
import ForMathlib.OptimalTransport.DroValueFunction
import ForMathlib.Analysis.Supergradient

set_option autoImplicit false

open MeasureTheory ForMathlib.Analysis

namespace ForMathlib.OT

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

/-- **The dual value is at most the DRO value function at the radius.** The heart of `hge`. -/
theorem dualValue_le_droValueAt
    (c : X → X → ℝ) (f : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ) (hδ : 0 < δ)
    (hfc : Continuous f) (hcc : Continuous fun p : X × X => c p.1 p.2)
    (hc0 : ∀ x y, 0 ≤ c x y) (C : ℝ) (hfb : ∀ x, |f x| ≤ C)
    (hbdd : ∀ lam : ℝ, 0 < lam → ∀ y, BddAbove (Set.range fun x => f x - lam * c x y))
    (hφ : ∀ lam : ℝ, 0 < lam →
        Integrable (fun y => ⨆ x, (f x - lam * c x y)) (ν : Measure X))
    (hne0 : (droValueSet c f ν 0).Nonempty) :
    sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
        v = lam * δ + expect ν (fun y => ⨆ x, (f x - lam * c x y)) }
      ≤ droValueAt c f ν δ := by
  classical
  have hfbC : ∀ x, f x ≤ C := fun x => (le_abs_self _).trans (hfb x)
  obtain ⟨lstar, hl0, hmul⟩ := exists_nonneg_multiplier' (s := Set.Ici (0:ℝ))
    (concaveOn_droValueAt (c := c) (f := f) (ν := ν) hfbC hne0)
    (monotoneOn_droValueAt (c := c) (f := f) (ν := ν) hfbC hne0)
    (a := 0) (b := δ + 1) (δ := δ) (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr (by linarith)) hδ (by linarith) (Set.mem_Ici.mpr hδ.le)
  obtain ⟨r₀, μ₀, π₀, hπ₀, hf₀, hc₀, hcost₀, hr₀⟩ := hne0
  have hcost₀' : couplingCost c π₀ = 0 :=
    le_antisymm hcost₀ (integral_nonneg fun z => hc0 z.1 z.2)
  -- the dual set is bounded below, by weak duality at the zero-cost plan
  have hBdd : BddBelow { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
      v = lam * δ + expect ν (fun y => ⨆ x, (f x - lam * c x y)) } := by
    refine ⟨expect μ₀ f, ?_⟩
    rintro v ⟨lam, hlam, rfl⟩
    have hkey := expect_le_dualIntegrand_add_lam_couplingCost c f lam hlam.le μ₀ ν π₀ hπ₀
      (hbdd lam hlam) hf₀ (by simpa only [sSup_range] using hφ lam hlam) hc₀
    simp only [sSup_range] at hkey
    rw [hcost₀', mul_zero, add_zero] at hkey
    nlinarith [hkey, hlam.le, hδ.le]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η : ℝ := min 1 (ε / (2 * δ)) with hηdef
  have hη : 0 < η := lt_min one_pos (div_pos hε (by linarith))
  have hηδ : η * δ ≤ ε / 2 := by
    have h1 : η ≤ ε / (2 * δ) := min_le_right _ _
    calc η * δ ≤ (ε / (2 * δ)) * δ := mul_le_mul_of_nonneg_right h1 hδ.le
      _ = ε / 2 := by field_simp
  set lam : ℝ := lstar + η with hlamdef
  have hlam : 0 < lam := by positivity
  obtain ⟨μ, π, hπ, hfμ, hcπ, hgel⟩ := exists_coupling_lagrangian_ge c f lam hlam ν hfc hcc C hfb
    (hbdd lam hlam) (hφ lam hlam) (show (0:ℝ) < ε / 2 by linarith)
  set t : ℝ := couplingCost c π with htdef
  have ht0 : 0 ≤ t := integral_nonneg fun z => hc0 z.1 z.2
  have hht : expect μ f ≤ droValueAt c f ν t :=
    le_csSup (bddAbove_droValueSet hfbC t) ⟨μ, π, hπ, hfμ, hcπ, le_rfl, rfl⟩
  have hmt : droValueAt c f ν t + lstar * (δ - t) ≤ droValueAt c f ν δ :=
    hmul t (Set.mem_Ici.mpr ht0)
  have hinf : sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
      v = lam * δ + expect ν (fun y => ⨆ x, (f x - lam * c x y)) }
      ≤ lam * δ + expect ν (fun y => ⨆ x, (f x - lam * c x y)) :=
    csInf_le hBdd ⟨lam, hlam, rfl⟩
  have hd : lam * δ - lam * t = lam * (δ - t) := by ring
  have h3 : lam * (δ - t) = lstar * (δ - t) + η * (δ - t) := by rw [hlamdef]; ring
  have h4 : η * (δ - t) ≤ η * δ := by nlinarith [ht0, hη.le]
  have h5 : expect μ f + lstar * (δ - t) ≤ droValueAt c f ν δ := by linarith [hht, hmt]
  linarith [hinf, hgel, hd, h3, h4, h5, hηδ]

omit [TopologicalSpace X] [SecondCountableTopology X] [Nonempty X] [BorelSpace X] in
/-- `h δ` is at most the DRO primal value: any plan of cost `≤ δ` witnesses `otCost ≤ δ`. -/
theorem droValueAt_le_droValue (c : X → X → ℝ) (f : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ)
    (hc0 : ∀ x y, 0 ≤ c x y) (C : ℝ) (hfb : ∀ x, f x ≤ C)
    (hne : (droValueSet c f ν δ).Nonempty)
    (hfint : ∀ μ : ProbabilityMeasure X, otCost c μ ν ≤ δ → Integrable f (μ : Measure X)) :
    droValueAt c f ν δ ≤ droValue { μ : ProbabilityMeasure X | otCost c μ ν ≤ δ } f := by
  refine csSup_le_csSup ?_ hne ?_
  · exact ForMathlib.OT.bddAbove_expect_set_of_bddAbove_range _ f ⟨C, by rintro _ ⟨x, rfl⟩; exact hfb x⟩
      hfint
  · rintro r ⟨μ, π, hπ, hfμ, hcπ, hcost, rfl⟩
    exact ⟨μ, le_trans (otCost_le_couplingCost c hc0 μ ν π hπ) hcost, rfl⟩

/-- **The duality gap is zero** (the `≥` direction), assembled from the three ingredients. -/
theorem dualValue_le_droValue
    (c : X → X → ℝ) (f : X → ℝ) (ν : ProbabilityMeasure X) (δ : ℝ) (hδ : 0 < δ)
    (hfc : Continuous f) (hcc : Continuous fun p : X × X => c p.1 p.2)
    (hc0 : ∀ x y, 0 ≤ c x y) (C : ℝ) (hfb : ∀ x, |f x| ≤ C)
    (hbdd : ∀ lam : ℝ, 0 < lam → ∀ y, BddAbove (Set.range fun x => f x - lam * c x y))
    (hφ : ∀ lam : ℝ, 0 < lam →
        Integrable (fun y => ⨆ x, (f x - lam * c x y)) (ν : Measure X))
    (hne0 : (droValueSet c f ν 0).Nonempty)
    (hfint : ∀ μ : ProbabilityMeasure X, otCost c μ ν ≤ δ → Integrable f (μ : Measure X)) :
    sInf { v : ℝ | ∃ lam : ℝ, 0 < lam ∧
        v = lam * δ + expect ν (fun y => ⨆ x, (f x - lam * c x y)) }
      ≤ droValue { μ : ProbabilityMeasure X | otCost c μ ν ≤ δ } f := by
  have hfbC : ∀ x, f x ≤ C := fun x => (le_abs_self _).trans (hfb x)
  refine le_trans (dualValue_le_droValueAt c f ν δ hδ hfc hcc hc0 C hfb hbdd hφ hne0) ?_
  exact droValueAt_le_droValue c f ν δ hc0 C hfbC
    (hne0.mono (subset_droValueSet hδ.le)) hfint


end ForMathlib.OT
