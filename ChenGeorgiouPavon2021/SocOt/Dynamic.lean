/-
# CGP SOC wrappers: dynamic/control side

This module contains the KL/SOC equivalence, Schrödinger-system interface,
Hopf--Cole control wrappers, and Hamilton--Jacobi/value-gradient wrappers.
-/

import ChenGeorgiouPavon2021.Continuum.Closure

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable (d : SBData X)

omit [NormedSpace ℝ X] in
/-- **SB as KL minimization ⇄ SB as control-energy minimization (CGP Problem 4.1 ⇄
Problem 4.3, via the energy identity (4.19)).**  Since the endpoint entropy
`D(ρ₀‖ρ₀^W)` is constant over the feasible set, minimizing `D(P‖W)` is equivalent to
minimizing the control energy, up to that additive constant. -/
theorem schrodingerBridge_KL_eq_SOC (ρ₀ ρ₁ : ProbabilityMeasure X)
    -- the energy identity (4.19) holds for every feasible control — bundled here as one edge,
    -- discharged per-`u` by `energy_identity` (its disintegration + finiteness + Cameron–Martin
    -- hypotheses); this theorem only needs the resulting identity, not how it is proved:
    (hEI : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
        klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
          = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
            + energy u (d.pathLaw u ρ₀))
    -- the feasible set is nonempty (a control steering ρ₀ → ρ₁ exists):
    (hne : ∃ u : Control X, Feasible d u ρ₀ ρ₁) :
    schrodingerBridgeValueKL d ρ₀ ρ₁
      = klReal (ρ₀ : Measure X) (initialMarginal d.R)
        + schrodingerBridgeValueSOC d ρ₀ ρ₁ := by
  -- the control energy is nonnegative (integrand ½‖u‖² ≥ 0)
  have henergy_nonneg : ∀ (u : Control X) (P : ProbabilityMeasure (Path X)), 0 ≤ energy u P := by
    intro u P
    refine integral_nonneg (fun ω => ?_)
    refine integral_nonneg (fun t => ?_)
    positivity
  -- energy identity + feasibility: D(P‖W) = D(ρ₀‖ρ₀^W) + energy, for each feasible u
  have hid : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
      klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
        = klReal (ρ₀ : Measure X) (initialMarginal d.R) + energy u (d.pathLaw u ρ₀) := by
    intro u hu
    rw [hEI u hu, hu.1]
  -- so the KL-value set is the SOC-value set translated by the constant endpoint entropy
  have hset : { J : ℝ | ∃ u : Control X, Feasible d u ρ₀ ρ₁ ∧
        J = klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) }
      = (fun x => klReal (ρ₀ : Measure X) (initialMarginal d.R) + x) ''
          { J : ℝ | ∃ u : Control X, Feasible d u ρ₀ ρ₁ ∧ J = energy u (d.pathLaw u ρ₀) } := by
    ext J
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨energy u (d.pathLaw u ρ₀), ⟨u, hu, rfl⟩, (hid u hu).symm⟩
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, (hid u hu).symm⟩
  -- sInf of a constant-translated set of reals
  have hshift : ∀ (a : ℝ) (T : Set ℝ), T.Nonempty → BddBelow T →
      sInf ((fun x => a + x) '' T) = a + sInf T := by
    intro a T hTne hTbdd
    have hImbdd : BddBelow ((fun x => a + x) '' T) := by
      obtain ⟨b, hb⟩ := hTbdd
      exact ⟨a + b, by rintro _ ⟨t, ht, rfl⟩; simp only; linarith [hb ht]⟩
    refine le_antisymm ?_ ?_
    · have hsub : sInf ((fun x => a + x) '' T) - a ≤ sInf T :=
        le_csInf hTne (fun t ht => by
          have := csInf_le hImbdd ⟨t, ht, rfl⟩; simp only at this; linarith)
      linarith
    · exact le_csInf (hTne.image _) (by rintro _ ⟨t, ht, rfl⟩; simp only; linarith [csInf_le hTbdd ht])
  obtain ⟨u₀, hu₀⟩ := hne
  have hSOCne : { J : ℝ | ∃ u : Control X, Feasible d u ρ₀ ρ₁ ∧ J = energy u (d.pathLaw u ρ₀) }.Nonempty :=
    ⟨energy u₀ (d.pathLaw u₀ ρ₀), u₀, hu₀, rfl⟩
  have hSOCbdd : BddBelow { J : ℝ | ∃ u : Control X, Feasible d u ρ₀ ρ₁ ∧ J = energy u (d.pathLaw u ρ₀) } :=
    ⟨0, by rintro _ ⟨u, _, rfl⟩; exact henergy_nonneg u (d.pathLaw u ρ₀)⟩
  unfold schrodingerBridgeValueKL schrodingerBridgeValueSOC
  rw [hset, hshift _ _ hSOCne hSOCbdd]

--------------------------------------------------------------------------------
-- §4  Schrödinger system (4.22) and the Hopf–Cole / Fleming optimal control
--------------------------------------------------------------------------------

/-- **The PDE Schrödinger system (CGP Problem 4.3, (4.22a)–(4.22d)).**
`φ` solves the *backward* heat equation and `φhat` the *forward* heat equation, with
the nonlinear boundary coupling `φ·φhat = ρ₀` at `t=0` and `= ρ₁` at `t=1`.

Abstracted: `lap` is the Laplacian `Δ`; `dens0`, `dens1` are the densities
`dρ₀/dx`, `dρ₁/dx`; `∂ₜ` is `deriv` in the time argument.

**Documentary (2026-07).** This structure records CGP (4.22) for reference; it is *not* a
hypothesis of any theorem here. In the real problem it is what establishes the Hopf–Cole
control `∇log φ` as optimal — but that consequence is exactly the (unformalized) SDE content
carried by the `hHC` verification edge of `optimal_control_eq_grad_log` et al., so taking the
raw system as a separate premise would be logically inert. -/
structure SchrodingerSystem (ε : ℝ) (lap : (X → ℝ) → X → ℝ)
    (φ φhat : ℝ → X → ℝ) (dens0 dens1 : X → ℝ) : Prop where
  /-- `∂ₜφ + (ε/2)Δφ = 0` — backward heat equation (CGP (4.22a)). -/
  backward : ∀ t x, deriv (fun s => φ s x) t + (ε / 2) * lap (φ t) x = 0
  /-- `∂ₜφ̂ − (ε/2)Δφ̂ = 0` — forward heat equation (CGP (4.22b)). -/
  forward : ∀ t x, deriv (fun s => φhat s x) t - (ε / 2) * lap (φhat t) x = 0
  /-- `φ(0,x)·φ̂(0,x) = ρ₀(x)` (CGP (4.22c)). -/
  boundary0 : ∀ x, φ 0 x * φhat 0 x = dens0 x
  /-- `φ(1,y)·φ̂(1,y) = ρ₁(y)` (CGP (4.22d)). -/
  boundary1 : ∀ x, φ 1 x * φhat 1 x = dens1 x

/-- `u` is **optimal for the SOC Schrödinger-bridge problem** (CGP Problem 4.3): it is
feasible and attains the SOC value `min_u J(u)`. -/
def IsOptimalSOC (u : Control X) (ρ₀ ρ₁ : ProbabilityMeasure X) : Prop :=
  Feasible d u ρ₀ ρ₁ ∧ energy u (d.pathLaw u ρ₀) = schrodingerBridgeValueSOC d ρ₀ ρ₁

omit [NormedSpace ℝ X] in
/-- **Optimal control = Hopf–Cole / Fleming logarithmic transform (CGP (4.21)).**
The optimal feedback control of Problem 4.3 is the gradient of `log φ`, where in the real
problem `φ` is the forward Schrödinger potential solving the system (4.22):
`u*(t,x) = ∇ log φ(t,x)`.

Abstracted: `grad = ∇`; `φ` is the (forward) Schrödinger potential.

**Soundness note (2026-07 audit).** As originally scaffolded this theorem was *false as
stated*: `grad` is a free operator argument, so with `grad := fun _ _ => 0` the hypotheses
stay satisfiable while the conclusion `u* = 0` fails — a bare `sorry` here could never be
discharged soundly (see `JOURNAL.md`). The faithful content of CGP (4.21) is the **verification
theorem** (the Hopf–Cole control `∇log φ` *is* optimal) plus **uniqueness** of the SOC optimizer;
both are genuine SDE/convexity facts absent from Mathlib, so — exactly as the strong-duality
equalities isolate their attainment edge — they are made explicit hypotheses (`hHC`, `huniq`) and
the stated identity is *derived*. With them the theorem is true and non-vacuous (in the real
problem `∇log φ` is optimal and the optimizer is unique); no free-operator counterexample
survives (`hHC` pins the candidate down).

**Minimal-hypothesis note (2026-07).** The Schrödinger-system hypothesis `hsys` (and the
operators `lap`, `φhat`, `dens0`, `dens1` it named) was **removed** as logically inert: it was
never used in the derivation, and keeping it falsely suggested the PDE structure was doing
logical work when `hHC` already encodes optimality of this specific `∇log φ`. The honest content
is `existence (hHC) + uniqueness (huniq) ⟹ characterization`. In the real problem `hHC` is
established *from* the Schrödinger system by the (unformalized) SDE verification; that step is
where (4.22) enters, and it lives inside `hHC`, not as a separate inert premise. -/
theorem optimal_control_eq_grad_log
    (grad : (X → ℝ) → X → X) (φ : ℝ → X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (u_star : Control X) (hopt : IsOptimalSOC d u_star ρ₀ ρ₁)
    -- CGP (4.21) verification: the Hopf–Cole control `∇log φ` is itself optimal (the SDE content
    -- that `∇log φ` steers `ρ₀→ρ₁` and attains the SOC minimum) — an explicit edge, not a `sorry`:
    (hHC : IsOptimalSOC d (fun t x => grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁)
    -- uniqueness of the SOC optimizer (strict convexity of the control energy) — an explicit edge:
    (huniq : ∀ u u' : Control X,
        IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u') :
    ∀ t x, u_star t x = grad (fun y => Real.log (φ t y)) x := by
  intro t x
  rw [huniq u_star _ hopt hHC]

/-- **Optimal control with diffusion scaling `σ` (CGP Theorem 5.2, (5.11a)).**
For the general controlled diffusion, the optimal control is `u* = σ'∇log φ`; in the
isotropic case `a = σσ' = σ²I` this reads
`u*(t,x) = σ²·∇ log φ(t,x)`.

Same soundness note as `optimal_control_eq_grad_log`: false as originally stated (free `grad`);
the verification (`hHC`: the scaled Hopf–Cole control is optimal) + uniqueness (`huniq`) edges make
it true and let the identity be derived. -/
theorem optimal_control_eq_sigma_grad_log
    (grad : (X → ℝ) → X → X) (φ : ℝ → X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (u_star : Control X) (hopt : IsOptimalSOC d u_star ρ₀ ρ₁)
    (hHC : IsOptimalSOC d (fun t x => (d.sigma ^ 2) • grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁)
    (huniq : ∀ u u' : Control X,
        IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u') :
    ∀ t x, u_star t x = (d.sigma ^ 2) • grad (fun y => Real.log (φ t y)) x := by
  intro t x
  rw [huniq u_star _ hopt hHC]

omit [NormedSpace ℝ X] in
/-- **Optimal control = negative value-gradient (DRSB reconciliation of CGP (4.21) /
Thm 5.2 (5.11a)).**  This is the key fact the DRSB value function `V` and its optimal
control rest on.  With the sign convention `V = −log φ` (equivalently `V = −λ = −ψ`;
CGP "Sign note", `V4.lean`), the Hopf–Cole optimal control at the initial time is the
negative gradient of the value function:
`u*(0,x) = −∇V(x)`.

Abstracted: `grad = ∇`; `φ` is the forward Schrödinger potential; the hypothesis
`hVlogφ` records the sign identification `V = −log φ`.

**Soundness note (2026-07 audit).** This theorem previously compiled *green but false*: its
proof `rw`s through `optimal_control_eq_grad_log`, which was itself false-as-stated (free `grad`),
so a `#print axioms` would show `sorryAx` and the stated `u*(0,·) = −∇V` was not actually a
theorem (`grad := 0` counterexample). It is now sound: it inherits the `hHC` (Hopf–Cole control
optimal) + `huniq` (optimizer unique) edges from `optimal_control_eq_grad_log` and threads them
through. With `grad := 0`, `hHC` forces `u* = 0` and the conclusion `u*(0,·) = −0 = 0` holds — no
counterexample survives. -/
theorem optimal_control_eq_neg_grad_value
    (grad : (X → ℝ) → X → X) (φ : ℝ → X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (u_star : Control X) (hopt : IsOptimalSOC d u_star ρ₀ ρ₁)
    -- the verification + uniqueness edges (inherited from `optimal_control_eq_grad_log`):
    (hHC : IsOptimalSOC d (fun t x => grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁)
    (huniq : ∀ u u' : Control X,
        IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u')
    -- sign identification of the cost-to-go with the log-potential (CGP "Sign note"):
    (hVlogφ : ∀ x, d.V x = - Real.log (φ 0 x))
    -- `∇` is additive/linear, so `∇(−V) = −∇V` (the property that makes the sign flip work):
    (hgrad_neg : grad (fun y => -(d.V y)) = fun x => -(grad d.V x)) :
    ∀ x, u_star 0 x = - grad d.V x := by
  intro x
  -- u*(0,x) = ∇log φ(0,x) (Hopf–Cole, `optimal_control_eq_grad_log`), and log φ(0,·) = −V
  rw [optimal_control_eq_grad_log d grad φ ρ₀ ρ₁ u_star hopt hHC huniq 0 x]
  have hφV : (fun y => Real.log (φ 0 y)) = (fun y => -(d.V y)) := by
    funext y; linarith [hVlogφ y]
  rw [hφV, hgrad_neg]

--------------------------------------------------------------------------------
-- §5  HJB / value-gradient control for OMT (CGP Prop 3.2)
--------------------------------------------------------------------------------

/-- **Hamilton–Jacobi equation for OMT (CGP Proposition 3.2, (3.20)).**
`∂ₜλ + ½‖∇λ‖² = 0`, for the value function / co-state `λ`.  Abstracted: `grad = ∇`. -/
def HamiltonJacobi (grad : (X → ℝ) → X → X) (lam : ℝ → X → ℝ) : Prop :=
  ∀ t x, deriv (fun s => lam s x) t + (1 / 2 : ℝ) * ‖grad (lam t) x‖ ^ 2 = 0

omit [NormedSpace ℝ X] in
/-- **Optimal control = value gradient (CGP Proposition 3.2, (3.16); (5.5)).**
For the value function / co-state `λ` (which in the real problem solves the Hamilton–Jacobi
equation (3.20), `HamiltonJacobi` above), the optimal control steering `ρ₀ → ρ₁` is the
gradient of the value function: `u*(t,x) = ∇λ(t,x)`.  This is the value-function form of the
Hopf–Cole control; with the log transform `λ = log φ` it matches (4.21) / Thm 5.2 (5.11a).

Abstracted: `grad = ∇`; `λ` is the value function / co-state.

Same soundness note as `optimal_control_eq_grad_log`: false as originally stated (free `grad`);
the verification (`hHC`: the value-gradient control `∇λ` is optimal) + uniqueness (`huniq`) edges
make it true and let the identity be derived.  The Hamilton–Jacobi hypothesis was **removed** as
logically inert (never used in the derivation): the HJ equation is *why* `∇λ` is optimal in the
real problem — that content lives inside `hHC`, not as a separate premise. -/
theorem optimal_control_eq_grad_value
    (grad : (X → ℝ) → X → X) (lam : ℝ → X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (u_star : Control X) (hopt : IsOptimalSOC d u_star ρ₀ ρ₁)
    (hHC : IsOptimalSOC d (fun t x => grad (lam t) x) ρ₀ ρ₁)
    (huniq : ∀ u u' : Control X,
        IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u') :
    ∀ t x, u_star t x = grad (lam t) x := by
  intro t x
  rw [huniq u_star _ hopt hHC]

--------------------------------------------------------------------------------

end ChenGeorgiouPavon2021
