import ChenGeorgiouPavon2021.EnergyIdentity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

/-- **Euler–Maruyama (discrete) energy identity — the card's actual measurement of (4.19).**

The DRSB card does not evaluate the continuous `energy_identity`; it evaluates the
**Euler–Maruyama discretization** (AGENTS §3: "exact `𝔼_μ[V]` → Euler–Maruyama SDE").
For the `N`-step discretization of `dX = u dt + √ε dW` (unit diffusion `ε = 1`, both chains
started at the same point so the endpoint-entropy term of (4.19) vanishes), the whitened
increments are a standard Gaussian on the `Fin N × ι` increment space, and the controlled
law is that Gaussian shifted by `emShift Δt u` (`√Δt·u_k` per step). The relative entropy of
the controlled vs. reference *path* law is then exactly the discrete control energy
`∑ₖ Δt·½‖u_k‖²` — the Riemann sum of `𝔼[∫₀¹ ½‖u_t‖² dt]`.

Proved, dependency-clean, by delegating to
`ForMathlib.MeasureTheory.klDiv_emShift_eq_emEnergy`, which is built on the **vendored**
Cameron–Martin lemma `klDiv_stdGaussian_map_add` (`KL(N(·+h) ‖ N) = ½‖h‖²`) from
`mrdouglasny/gibbs-variational` (Apache-2.0; see that file's header + README).  This is the
discrete/Gaussian layer of the (still-open) continuous `energy_identity` above; the only
remaining edge is the `Δt → 0` SDE limit (T4; PROOF_PIPELINE §2). -/
theorem energy_identity_euler_maruyama {ι : Type*} [Fintype ι] {N : ℕ} {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (u : Fin N → ι → ℝ) :
    klReal ((ForMathlib.MeasureTheory.stdGaussian (Fin N × ι)).map
          (· + ForMathlib.MeasureTheory.emShift Δt u))
        (ForMathlib.MeasureTheory.stdGaussian (Fin N × ι))
      = ForMathlib.MeasureTheory.emEnergy Δt u := by
  unfold klReal
  exact ForMathlib.MeasureTheory.klDiv_emShift_eq_emEnergy hΔt u

/-- **Deterministic Cameron--Martin energy identity — sequence model.**
For the canonical iid standard-Gaussian sequence law, translating by a square-summable
coordinate vector `c` has relative entropy exactly `½‖c‖²_{ℓ²}`.

This is the sequence-coordinate Cameron--Martin content staged by
`ForMathlib.MeasureTheory.GaussianCameronMartin`.  It does not by itself discharge the
path-kernel `hCM` edge in `energy_identity`: identifying CGP/SDE path kernels with this
sequence model is the later Wiener/path-transport step. -/
theorem energy_identity_sequenceModel (c : ℕ → ℝ)
    (hc : Summable (fun n : ℕ => c n ^ 2)) :
    klReal (ForMathlib.MeasureTheory.stdSeqGaussian.map (fun x : ℕ → ℝ => x + c))
        ForMathlib.MeasureTheory.stdSeqGaussian
      = 2⁻¹ * ∑' n : ℕ, c n ^ 2 := by
  unfold klReal
  simpa [ForMathlib.MeasureTheory.cmTotalEnergy] using
    ForMathlib.MeasureTheory.toReal_klDiv_stdSeqGaussian_map_add_of_summable c hc


/-- **Sequence-model finite-KL criterion.**
For the canonical iid standard-Gaussian sequence law, the translated law has finite
relative entropy exactly when the translation vector is square-summable.

This wrapper is proved directly from the already-built finite and converse branch
lemmas, rather than through the newer packaged iff theorem.  That keeps the file
check robust when `Basic.lean` is checked with `lake env lean` before rebuilding the
fresh `GaussianCameronMartin.olean`. -/
theorem energy_identity_sequenceModel_finite_iff_summable (c : Nat -> Real) :
    Iff
      (Ne
        (InformationTheory.klDiv
          (ForMathlib.MeasureTheory.stdSeqGaussian.map (fun x : Nat -> Real => x + c))
          ForMathlib.MeasureTheory.stdSeqGaussian)
        Top.top)
      (Summable (fun n : Nat => c n ^ 2)) := by
  constructor
  · intro hfin
    haveI : IsProbabilityMeasure
        (ForMathlib.MeasureTheory.stdSeqGaussian.map (fun x : Nat -> Real => x + c)) :=
      Measure.isProbabilityMeasure_map
        (ForMathlib.MeasureTheory.measurable_shift c).aemeasurable
    exact ForMathlib.MeasureTheory.summable_of_shift_kl_finite_of_ac c
      (InformationTheory.klDiv_ne_top_iff.mp hfin).1 hfin
  · intro hsum
    exact ForMathlib.MeasureTheory.klDiv_stdSeqGaussian_map_add_ne_top_of_summable c hsum

/-- **Sequence-model infinite-KL criterion.**
For the canonical iid standard-Gaussian sequence law, nonsquare-summable translations
have infinite relative entropy. -/
theorem energy_identity_sequenceModel_top_iff_not_summable (c : Nat -> Real) :
    Iff
      (InformationTheory.klDiv
        (ForMathlib.MeasureTheory.stdSeqGaussian.map (fun x : Nat -> Real => x + c))
        ForMathlib.MeasureTheory.stdSeqGaussian = Top.top)
      (Not (Summable (fun n : Nat => c n ^ 2))) := by
  constructor
  · intro htop hsum
    exact (ForMathlib.MeasureTheory.klDiv_stdSeqGaussian_map_add_ne_top_of_summable c hsum) htop
  · intro hnsum
    by_contra hne_top
    exact hnsum ((energy_identity_sequenceModel_finite_iff_summable c).mp hne_top)



end ChenGeorgiouPavon2021
