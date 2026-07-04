/-
# Chen, Georgiou, Pavon (2021) — "Stochastic control liaisons: Richard Sinkhorn
  meets Gaspard Monge on a Schrödinger bridge" (arXiv:2005.10963).

Core theorems of the Schrödinger-bridge ⇄ stochastic-optimal-control ⇄
entropic-optimal-transport backbone that *defines* the DRSB value function
`V(x) = 𝔼[∫₀¹ ½‖u_t‖² dt + ρ g(X₁) | X₀ = x]` and its optimal control
`u* = σ²∇log φ = −∇V`.

Statements only — every proof body is `sorry`; no `axiom`s.

Prose source (printed Problem / Theorem / equation numbers are CGP arXiv:2005.10963 v3):
`prose/schrodinger-bridge-soc-ot.md`, Part I (Chen–Georgiou–Pavon).

## Abstracted analysis objects (not in Mathlib)

Full SDE / path-measure / PDE machinery is not in Mathlib, so — exactly as the
task and the reference `Dynamics` structure do — the analytic data is carried by an
abstract `structure SBData` and by abstract operators passed as hypotheses:

* `SBData.R`        — the reference (prior) path law, Wiener measure `W^ε` (CGP §I.0, (4.1')).
* `SBData.pathLaw`  — the controlled path law `P^{u,μ}` of `dX = u dt + √ε dW` (CGP Problem 4.3, (4.20)).
* `SBData.sigma`    — the diffusion coefficient `σ` (isotropic `a = σσ' = σ²I`, CGP Thm 5.2); `ε = σ²`.
* `SBData.f`        — the prior/reference drift field `f` (CGP Prop 3.4 (3.26), Thm 5.2 (5.8)).
* `grad`, `lap`     — abstract gradient `∇` and Laplacian `Δ` operators (passed as hypotheses).
* `φ`, `φhat`, `λ`  — Schrödinger potentials / co-state (space-time functions `ℝ → X → ℝ`).
* `negEntropy`, `p`, `dens_star` — abstract entropy functional and coupling/transition densities.

Each abstracted object is flagged inline at its use site.
-/
import Mathlib
import ForMathlib.LinearAlgebra.Matrix.SinkhornScaling
import ForMathlib.MeasureTheory.GaussianEntropy
import ForMathlib.MeasureTheory.KLDataProcessing

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ChenGeorgiouPavon2021

--------------------------------------------------------------------------------
-- Ambient space and basic path/control types
--------------------------------------------------------------------------------

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Path space (placeholder): paths are functions `ℝ → X`.  In CGP the domain is
`[0,1]`; here `t` ranges over `ℝ` and only `t ∈ [0,1]` is used (CGP §I.0,
`Ω = C([0,1];ℝⁿ)`). -/
abbrev Path (X : Type*) : Type _ := ℝ → X

/-- Control / feedback drift `u(t,x)` (CGP Problem 4.3, (4.20)). -/
abbrev Control (X : Type*) : Type _ := ℝ → X → X

--------------------------------------------------------------------------------
-- §1  The SB / SOC data (abstract interface; mirrors reference `Dynamics`)
--------------------------------------------------------------------------------

/-- **SB / SOC data.**  The Schrödinger-bridge / stochastic-optimal-control problem
data, abstracting the SDE and path-measure machinery that is not in Mathlib.

Fields (each corresponds to a CGP object, see the file header):
* `R`        — reference/prior path law `W^ε` (CGP §I.0);
* `pathLaw`  — controlled path law `P^{u,μ}` of `dX = u dt + √ε dW` (CGP (4.20));
* `sigma`    — diffusion coefficient `σ`, with `a = σ²I` and `ε = σ²` (CGP Thm 5.2);
* `f`        — prior drift field `f` (CGP Prop 3.4 (3.26));
* `runningCost` — running (Lagrangian) cost integrand `L(u,x) = ½‖u‖²` (CGP (4.20));
* `g`        — terminal cost `g` (DRSB terminal penalty);
* `rho`      — terminal weight `ρ`;
* `V`        — value function / minimized cost-to-go `V` (CGP co-state `λ`, `V = −λ = −log φ`). -/
structure SBData (X : Type*) [MeasurableSpace X] [NormedAddCommGroup X] where
  /-- Reference/prior path law `W^ε` (CGP §I.0, (4.1')). -/
  R : ProbabilityMeasure (Path X)
  /-- Controlled path law `P^{u,μ}` of `dX = u dt + √ε dW` (CGP Problem 4.3, (4.20)). -/
  pathLaw : Control X → ProbabilityMeasure X → ProbabilityMeasure (Path X)
  /-- Diffusion coefficient `σ`; `a = σσ' = σ²I`, `ε = σ²` (CGP §I.0, Thm 5.2). -/
  sigma : ℝ
  /-- Prior/reference drift field `f` (CGP Prop 3.4 (3.26), Thm 5.2 (5.8)). -/
  f : Control X
  /-- Running (Lagrangian) cost integrand `L(u,x) = ½‖u‖²` (CGP (4.20)). -/
  runningCost : Control X → X → ℝ
  /-- Terminal cost `g` (DRSB terminal penalty `ρ g(X₁)`). -/
  g : X → ℝ
  /-- Terminal weight `ρ`. -/
  rho : ℝ
  /-- Value function / minimized cost-to-go `V` (CGP co-state `λ`; `V = −λ = −log φ`). -/
  V : X → ℝ

variable (d : SBData X)

--------------------------------------------------------------------------------
-- §2  Energy, marginals, KL, feasibility, and the two SB values
--------------------------------------------------------------------------------

/-- Quadratic control energy `J(u) = 𝔼_P[∫₀¹ ½‖u_t‖² dt]` under a path law `P`
(CGP Problem 4.3, (4.20); energy term of (4.19)). -/
noncomputable def energy (u : Control X) (P : ProbabilityMeasure (Path X)) : ℝ :=
  ∫ ω, (∫ t in Set.Icc (0 : ℝ) 1, (1 / 2 : ℝ) * ‖u t (ω t)‖ ^ 2 ∂volume)
    ∂(P : Measure (Path X))

/-- Time-`t` marginal `(X_t)_# P` of a path law (as a `Measure`). -/
noncomputable def marginal (t : ℝ) (P : ProbabilityMeasure (Path X)) : Measure X :=
  Measure.map (fun ω : Path X => ω t) (P : Measure (Path X))

/-- Initial marginal `X₀`, `ρ₀`. -/
noncomputable def initialMarginal (P : ProbabilityMeasure (Path X)) : Measure X :=
  marginal 0 P

/-- Terminal marginal `X₁`, `ρ₁`. -/
noncomputable def terminalMarginal (P : ProbabilityMeasure (Path X)) : Measure X :=
  marginal 1 P

/-- Real-valued relative entropy / KL divergence `D(P‖Q) = 𝔼_P[log dP/dQ]`
(CGP unnumbered display before (4.6)), via `(klDiv P Q).toReal`.  Treating KL as a
real number implicitly assumes `klDiv P Q ≠ ⊤`; add that hypothesis where needed. -/
noncomputable def klReal {α : Type*} [MeasurableSpace α] (P Q : Measure α) : ℝ :=
  (InformationTheory.klDiv P Q).toReal

/-- **Feasibility for the SB problem.**  A control `u` steers `ρ₀ → ρ₁`: the
controlled path law `P^{u,ρ₀}` has initial marginal `ρ₀` and terminal marginal `ρ₁`
(the endpoint constraints `P₀ = ρ₀`, `P₁ = ρ₁` of CGP `𝒟(ρ₀,ρ₁)`, §I.0). -/
def Feasible (u : Control X) (ρ₀ ρ₁ : ProbabilityMeasure X) : Prop :=
  initialMarginal (d.pathLaw u ρ₀) = (ρ₀ : Measure X)
    ∧ terminalMarginal (d.pathLaw u ρ₀) = (ρ₁ : Measure X)

/-- **Schrödinger Bridge value, KL form (CGP Problem 4.1, (4.3)).**
`min { D(P‖W) : P ∈ 𝒟(ρ₀,ρ₁) }`, here as the infimum of `D(P^{u,ρ₀}‖R)` over
feasible controls. -/
noncomputable def schrodingerBridgeValueKL (ρ₀ ρ₁ : ProbabilityMeasure X) : ℝ :=
  sInf { J : ℝ | ∃ u : Control X,
    Feasible d u ρ₀ ρ₁ ∧ J = klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) }

/-- **Schrödinger Bridge value, stochastic-control form (CGP Problem 4.3, (4.20)).**
`min_u J(u) = 𝔼[∫₀¹ ½‖u_t‖² dt]` over controls steering `ρ₀ → ρ₁`. -/
noncomputable def schrodingerBridgeValueSOC (ρ₀ ρ₁ : ProbabilityMeasure X) : ℝ :=
  sInf { J : ℝ | ∃ u : Control X,
    Feasible d u ρ₀ ρ₁ ∧ J = energy u (d.pathLaw u ρ₀) }

--------------------------------------------------------------------------------
-- §3  Energy identity (4.19) and KL ⇄ SOC equivalence (Problem 4.1 ⇄ 4.3)
--------------------------------------------------------------------------------

/-- Abstract predicate: `P = pathLaw u ρ₀` is a **finite-energy diffusion** with Itô
differential `dX = u dt + √ε dW` (CGP (4.4)–(4.5)): `𝔼_P ∫₀¹‖u_t‖² dt < ∞`.  Under
this condition Girsanov's martingale term has zero expectation and the energy
identity (4.19) holds. -/
def FiniteEnergyDiffusion (u : Control X) (ρ₀ : ProbabilityMeasure X) : Prop :=
  Integrable (fun ω : Path X => ∫ t in Set.Icc (0 : ℝ) 1, ‖u t (ω t)‖ ^ 2 ∂volume)
    (d.pathLaw u ρ₀ : Measure (Path X))

/-- **Energy identity (CGP (4.19)).**  By Girsanov, for a finite-energy diffusion
`P = P^{u,ρ₀}`,
`D(P‖W) = D(ρ₀‖ρ₀^W) + 𝔼_P[∫₀¹ ½‖u_t‖² dt]`,
i.e. relative entropy splits into a constant endpoint term plus the control energy.

Still a bare `sorry`: the continuous statement needs multi-dimensional controlled-diffusion
Girsanov + KL between path measures, absent from Mathlib (T4; AGENTS §6, PROOF_PIPELINE §2).
The **discrete / Euler–Maruyama layer** — the actual card measurement (AGENTS §3) — is
proved sorry-free in `energy_identity_euler_maruyama` below, from the vendored Cameron–Martin
identity. The remaining gap is exactly the `Δt → 0` SDE limit. -/
theorem energy_identity (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hfe : FiniteEnergyDiffusion d u ρ₀) :
    klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
      = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
        + energy u (d.pathLaw u ρ₀) := by
  sorry

/-- **Euler–Maruyama (discrete) energy identity — the card's actual measurement of (4.19).**

The DRSB card does not evaluate the continuous `energy_identity`; it evaluates the
**Euler–Maruyama discretization** (AGENTS §3: "exact `𝔼_μ[V]` → Euler–Maruyama SDE").
For the `N`-step discretization of `dX = u dt + √ε dW` (unit diffusion `ε = 1`, both chains
started at the same point so the endpoint-entropy term of (4.19) vanishes), the whitened
increments are a standard Gaussian on the `Fin N × ι` increment space, and the controlled
law is that Gaussian shifted by `emShift Δt u` (`√Δt·u_k` per step). The relative entropy of
the controlled vs. reference *path* law is then exactly the discrete control energy
`∑ₖ Δt·½‖u_k‖²` — the Riemann sum of `𝔼[∫₀¹ ½‖u_t‖² dt]`.

Proved sorry-free, axiom-clean, by delegating to
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

/-- **SB as KL minimization ⇄ SB as control-energy minimization (CGP Problem 4.1 ⇄
Problem 4.3, via the energy identity (4.19)).**  Since the endpoint entropy
`D(ρ₀‖ρ₀^W)` is constant over the feasible set, minimizing `D(P‖W)` is equivalent to
minimizing the control energy, up to that additive constant. -/
theorem schrodingerBridge_KL_eq_SOC (ρ₀ ρ₁ : ProbabilityMeasure X)
    -- every feasible control is a finite-energy diffusion (CGP (4.4)–(4.5)):
    (hfe : ∀ u : Control X, Feasible d u ρ₀ ρ₁ → FiniteEnergyDiffusion d u ρ₀)
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
    rw [energy_identity d u ρ₀ (hfe u hu), hu.1]
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
`dρ₀/dx`, `dρ₁/dx`; `∂ₜ` is `deriv` in the time argument. -/
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

/-- **Optimal control = Hopf–Cole / Fleming logarithmic transform (CGP (4.21)).**
The optimal feedback control of Problem 4.3 is the gradient of `log φ`, where
`(φ, φhat)` solve the Schrödinger system (4.22):
`u*(t,x) = ∇ log φ(t,x)`.

Abstracted: `grad = ∇`, `lap = Δ`; `dens0`, `dens1` are the endpoint densities.

**Soundness note (2026-07 audit).** As originally scaffolded this theorem was *false as
stated*: `grad` is a free operator argument, so with `grad := fun _ _ => 0` the hypotheses
stay satisfiable while the conclusion `u* = 0` fails — a bare `sorry` here could never be
discharged soundly (see `JOURNAL.md`). The faithful content of CGP (4.21) is the **verification
theorem** (the Hopf–Cole control `∇log φ` *is* optimal) plus **uniqueness** of the SOC optimizer;
both are genuine SDE/convexity facts absent from Mathlib, so — exactly as the strong-duality
equalities isolate their attainment edge — they are made explicit hypotheses (`hHC`, `huniq`) and
the stated identity is *derived*. With them the theorem is true and non-vacuous (in the real
problem `∇log φ` is optimal and the optimizer is unique); no free-operator counterexample
survives (`hHC` pins the candidate down). -/
theorem optimal_control_eq_grad_log
    (grad : (X → ℝ) → X → X) (lap : (X → ℝ) → X → ℝ)
    (φ φhat : ℝ → X → ℝ) (dens0 dens1 : X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hsys : SchrodingerSystem (d.sigma ^ 2) lap φ φhat dens0 dens1)
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
    (grad : (X → ℝ) → X → X) (lap : (X → ℝ) → X → ℝ)
    (φ φhat : ℝ → X → ℝ) (dens0 dens1 : X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hsys : SchrodingerSystem (d.sigma ^ 2) lap φ φhat dens0 dens1)
    (u_star : Control X) (hopt : IsOptimalSOC d u_star ρ₀ ρ₁)
    (hHC : IsOptimalSOC d (fun t x => (d.sigma ^ 2) • grad (fun y => Real.log (φ t y)) x) ρ₀ ρ₁)
    (huniq : ∀ u u' : Control X,
        IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u') :
    ∀ t x, u_star t x = (d.sigma ^ 2) • grad (fun y => Real.log (φ t y)) x := by
  intro t x
  rw [huniq u_star _ hopt hHC]

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
    (grad : (X → ℝ) → X → X) (lap : (X → ℝ) → X → ℝ)
    (φ φhat : ℝ → X → ℝ) (dens0 dens1 : X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hsys : SchrodingerSystem (d.sigma ^ 2) lap φ φhat dens0 dens1)
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
  rw [optimal_control_eq_grad_log d grad lap φ φhat dens0 dens1 ρ₀ ρ₁ hsys u_star hopt hHC huniq 0 x]
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

/-- **Optimal control = value gradient (CGP Proposition 3.2, (3.16); (5.5)).**
If `λ` solves the Hamilton–Jacobi equation (3.20) and `u*` is the optimal control
steering `ρ₀ → ρ₁`, then the optimal feedback is the gradient of the value function /
co-state: `u*(t,x) = ∇λ(t,x)`.  This is the value-function form of the Hopf–Cole
control; with the log transform `λ = log φ` it matches (4.21) / Thm 5.2 (5.11a).

Abstracted: `grad = ∇`; `λ` is the value function / co-state.

Same soundness note as `optimal_control_eq_grad_log`: false as originally stated (free `grad`);
the verification (`hHC`: the value-gradient control `∇λ` is optimal) + uniqueness (`huniq`) edges
make it true and let the identity be derived. -/
theorem optimal_control_eq_grad_value
    (grad : (X → ℝ) → X → X) (lam : ℝ → X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hHJ : HamiltonJacobi grad lam)
    (u_star : Control X) (hopt : IsOptimalSOC d u_star ρ₀ ρ₁)
    (hHC : IsOptimalSOC d (fun t x => grad (lam t) x) ρ₀ ρ₁)
    (huniq : ∀ u u' : Control X,
        IsOptimalSOC d u ρ₀ ρ₁ → IsOptimalSOC d u' ρ₀ ρ₁ → u = u') :
    ∀ t x, u_star t x = grad (lam t) x := by
  intro t x
  rw [huniq u_star _ hopt hHC]

--------------------------------------------------------------------------------
-- §6  Static problem, entropic OT / Sinkhorn (CGP §I.2–I.3, §7–§8)
--------------------------------------------------------------------------------

/-- Set of couplings `Π(ρ₀,ρ₁)`: joint laws on `X × X` with first marginal `ρ₀` and
second marginal `ρ₁` (CGP §I.0). -/
def couplings (ρ₀ ρ₁ : ProbabilityMeasure X) : Set (ProbabilityMeasure (X × X)) :=
  { π | Measure.map Prod.fst (π : Measure (X × X)) = (ρ₀ : Measure X)
      ∧ Measure.map Prod.snd (π : Measure (X × X)) = (ρ₁ : Measure X) }

/-- Endpoint law `R₀₁ = (X₀,X₁)_# R` of the reference path measure (CGP §I.2). -/
noncomputable def endpointLaw : Measure (X × X) :=
  Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.R : Measure (Path X))

/-- **Static Schrödinger value (CGP Problem 4.2, (4.7)).**
`min { D(ρ₀₁‖ρ₀₁^W) : ρ₀₁ ∈ Π(ρ₀,ρ₁) }` — the reduction of Problem 4.1 to a static
coupling problem. -/
noncomputable def staticSBValue (ρ₀ ρ₁ : ProbabilityMeasure X) : ℝ :=
  sInf { J : ℝ | ∃ π : ProbabilityMeasure (X × X),
    π ∈ couplings ρ₀ ρ₁ ∧ J = klReal (π : Measure (X × X)) (endpointLaw d) }

/-- **Dynamic ⇄ static Schrödinger equivalence (CGP Problem 4.1 ⇄ Problem 4.2,
(4.6)/(4.8); Léonard Prop 2.3).**  The infimum over path measures equals the infimum
over couplings: gluing the reference bridges `W_{xy}` onto the optimal coupling gives
the optimal path law.

**Proof (house pattern — `le_antisymm(gluing-edge, DPI-proved)`).** One direction is
now **genuinely proved**: `staticSBValue ≤ schrodingerBridgeValueKL`, via the **data-processing
inequality** for KL. The endpoint projection `e : ω ↦ (ω₀, ω₁)` sends any feasible path law
`P = P^{u,ρ₀}` to a coupling `e_# P ∈ Π(ρ₀,ρ₁)` (its two marginals are `initialMarginal P = ρ₀`
and `terminalMarginal P = ρ₁`, by feasibility), and coarse-graining cannot increase relative
entropy — `D(e_# P ‖ e_# R) ≤ D(P ‖ R)` with `e_# R = R₀₁ = endpointLaw` — so
`staticSBValue ≤ D(e_# P ‖ R₀₁) ≤ D(P ‖ R)`; taking the infimum over feasible `u` gives the
bound. The DPI is the new axiom-clean `ForMathlib.MeasureTheory.toReal_klDiv_map_le` (a genuine
Mathlib gap, proved by conditional Jensen on the convex KL generator). The honest regularity
edges are `hac`/`hfin` (each feasible path law is `≪ R` with finite relative entropy — the
finite-energy diffusion regime) and `hne` (the feasible set is nonempty).

The reverse `schrodingerBridgeValueKL ≤ staticSBValue` (**gluing** the reference bridges
`W_{xy}` onto a coupling to reconstruct a path law of equal relative entropy — Léonard Prop 2.3)
is the disintegration/path-space-reconstruction content absent from Mathlib; it is isolated to
the single explicit edge `hglue`, exactly as the strong-duality equalities isolate their
attainment edge. -/
theorem dynamic_eq_static_SB (ρ₀ ρ₁ : ProbabilityMeasure X)
    -- each feasible path law is absolutely continuous w.r.t. the reference with finite relative
    -- entropy (the finite-energy diffusion regime; cf. `FiniteEnergyDiffusion`):
    (hac : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
        (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : ∀ u : Control X, Feasible d u ρ₀ ρ₁ →
        InformationTheory.klDiv (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    -- the feasible set is nonempty (a control steering ρ₀ → ρ₁ exists):
    (hne : ∃ u : Control X, Feasible d u ρ₀ ρ₁)
    -- the gluing / path-reconstruction edge (Léonard Prop 2.3; the ≤ direction, isolated):
    (hglue : schrodingerBridgeValueKL d ρ₀ ρ₁ ≤ staticSBValue d ρ₀ ρ₁) :
    schrodingerBridgeValueKL d ρ₀ ρ₁ = staticSBValue d ρ₀ ρ₁ := by
  refine le_antisymm hglue ?_
  -- the data-processing direction: staticSBValue ≤ schrodingerBridgeValueKL
  obtain ⟨u₀, hu₀⟩ := hne
  refine le_csInf ⟨_, u₀, hu₀, rfl⟩ ?_
  rintro J ⟨u, hu, rfl⟩
  -- the endpoint projection e : ω ↦ (ω 0, ω 1)
  have he : Measurable (fun ω : Path X => (ω (0 : ℝ), ω (1 : ℝ))) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  haveI hπprob : IsProbabilityMeasure
      (Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.pathLaw u ρ₀ : Measure (Path X))) :=
    Measure.isProbabilityMeasure_map he.aemeasurable
  set πP : ProbabilityMeasure (X × X) :=
    ⟨Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.pathLaw u ρ₀ : Measure (Path X)), hπprob⟩
    with hπP
  have hπcoe : (πP : Measure (X × X))
      = Measure.map (fun ω : Path X => (ω 0, ω 1)) (d.pathLaw u ρ₀ : Measure (Path X)) := rfl
  -- e_# P is a coupling of (ρ₀, ρ₁), by feasibility of u
  have hcoupl : πP ∈ couplings ρ₀ ρ₁ := by
    constructor
    · rw [hπcoe, Measure.map_map measurable_fst he]
      exact hu.1
    · rw [hπcoe, Measure.map_map measurable_snd he]
      exact hu.2
  -- data-processing: D(e_# P ‖ endpointLaw) ≤ D(P ‖ R)
  have hdpi : klReal (πP : Measure (X × X)) (endpointLaw d)
      ≤ klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) :=
    ForMathlib.MeasureTheory.toReal_klDiv_map_le
      (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) (hac u hu)
      (fun ω => (ω 0, ω 1)) he (hfin u hu)
  -- staticSBValue ≤ D(e_# P ‖ endpointLaw) ≤ D(P ‖ R)
  refine le_trans ?_ hdpi
  refine csInf_le ⟨0, ?_⟩ ⟨πP, hcoupl, rfl⟩
  rintro _ ⟨π, _, rfl⟩
  exact ENNReal.toReal_nonneg

/-- Quadratic transport cost `∫∫ ½‖x−y‖² dπ` of a coupling (CGP (4.9)–(4.10)). -/
noncomputable def transportCostHalfSq (π : ProbabilityMeasure (X × X)) : ℝ :=
  ∫ z, (1 / 2 : ℝ) * ‖z.1 - z.2‖ ^ 2 ∂(π : Measure (X × X))

/-- **Entropic regularization of OMT (CGP (4.10)).**  The Schrödinger bridge is an
entropic regularization of quadratic OMT: the objective is
`∫∫ ½‖x−y‖² dπ + ε ∫∫ π log π`.

Abstracted: `negEntropy π = ∫∫ π(x,y) log π(x,y) dx dy` is carried abstractly (it
requires the coupling density). As `ε → 0` this reduces to the Kantorovich cost. -/
noncomputable def entropicRegOMTObjective (ε : ℝ)
    (negEntropy : ProbabilityMeasure (X × X) → ℝ) (π : ProbabilityMeasure (X × X)) : ℝ :=
  transportCostHalfSq π + ε * negEntropy π

/-- **Entropic-OT value = static SB against the Gibbs kernel (CGP §7, (7.13)).**
`min { D(π‖π_B) : π ∈ Π(ρ₀,ρ₁) }` with `π_B ∝ exp(−c/ε)` the Boltzmann/Gibbs kernel
(CGP (7.10),(7.14)). -/
noncomputable def entropicOTValue (πB : ProbabilityMeasure (X × X))
    (ρ₀ ρ₁ : ProbabilityMeasure X) : ℝ :=
  sInf { J : ℝ | ∃ π : ProbabilityMeasure (X × X),
    π ∈ couplings ρ₀ ρ₁ ∧ J = klReal (π : Measure (X × X)) (πB : Measure (X × X)) }

/-- **Static SB = entropic OT (CGP §I.3 / §7, (4.9)–(4.10), (7.13)).**  When the
reference endpoint law is the Gibbs kernel `ρ₀₁^W = π_B ∝ exp(−c/ε)`, the static
Schrödinger problem (4.7) coincides with the entropic-OT / Sinkhorn problem (7.13). -/
theorem staticSB_eq_entropicOT (πB : ProbabilityMeasure (X × X))
    (ρ₀ ρ₁ : ProbabilityMeasure X)
    (hgibbs : (πB : Measure (X × X)) = endpointLaw d) :
    staticSBValue d ρ₀ ρ₁ = entropicOTValue πB ρ₀ ρ₁ := by
  -- Both values are `sInf` over the SAME coupling set of `klReal π (·)`; with the
  -- Gibbs-kernel identification `πB = R₀₁` the two reference measures coincide, so the
  -- objective — hence the whole infimum — is identical. (Content-free once the endpoint
  -- law IS the entropic-OT reference; the mathematics is (7.13)'s setup, not this rewrite.)
  simp only [staticSBValue, entropicOTValue, hgibbs]

/-- **Product-form (Schrödinger factorization) of the optimal coupling (CGP (4.11);
static form (7.17)).**  The optimal coupling density factors as
`ρ*₀₁(x,y) = φ̂(x)·p(0,x,1,y)·φ(y)`, with `(φ̂,φ)` solving the Schrödinger system.

`φhat0`, `φ1` are the Schrödinger potentials. The reference transition density `p` is the
density of the reference endpoint law `R₀₁ = endpointLaw` w.r.t. Lebesgue, so *relative to
`R₀₁`* the optimal coupling's density is just the potential product `φ̂(x)·φ(y)` — the form used
here (`dπ*/dR₀₁ = φ̂(x)·φ(y)`, i.e. `π* = R₀₁.withDensity (φ̂(x)·φ(y))`); multiplying by
`dR₀₁/dLeb = p` recovers the printed `φ̂·p·φ` form.

**Soundness note (2026-07 audit).** As originally scaffolded this was *false as stated*: it
asserted a pointwise identity `∀ x y, dens_star(x,y) = φhat0 x · p x y · φ1 y` with `dens_star`,
`p`, `φhat0`, `φ1` all free (counterexample `dens_star := 0`), and a pointwise-everywhere density
identity is anyway ill-typed (densities are only a.e.-defined). Reformulated to the well-typed
**measure** identity `π* = R₀₁.withDensity (φ̂(x)·φ(y))`, derived — as everywhere else — by
isolating the genuine content to explicit edges: the **verification** that the product-form
coupling `π_prod` is feasible and optimal (`hprodfeas`, `hprodopt`; the Schrödinger structure of
CGP (4.11)) and **uniqueness** of the KL-projection optimizer (`huniq`; strict convexity of KL
over `Π(ρ₀,ρ₁)`). Given them, `π* = π_prod` and `π_prod`'s density is the product (`hπprod`). -/
theorem optimal_coupling_factorization
    (φhat0 φ1 : X → ℝ)
    (ρ₀ ρ₁ : ProbabilityMeasure X) (π_star π_prod : ProbabilityMeasure (X × X))
    -- π_star is the static Schrödinger optimizer (Problem 4.2):
    (hfeas : π_star ∈ couplings ρ₀ ρ₁)
    (hopt : klReal (π_star : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁)
    -- π_prod is the Schrödinger product-form coupling: `dπ_prod/dR₀₁ = φ̂(x)·φ(y)` (CGP (4.11)):
    (hπprod : (π_prod : Measure (X × X))
        = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2)))
    -- verification: the product-form coupling is feasible and optimal (the SDE/OT content):
    (hprodfeas : π_prod ∈ couplings ρ₀ ρ₁)
    (hprodopt : klReal (π_prod : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁)
    -- uniqueness of the KL-projection optimizer (strict convexity of KL over the coupling set):
    (huniq : ∀ π π' : ProbabilityMeasure (X × X),
        π ∈ couplings ρ₀ ρ₁ →
        klReal (π : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ →
        π' ∈ couplings ρ₀ ρ₁ →
        klReal (π' : Measure (X × X)) (endpointLaw d) = staticSBValue d ρ₀ ρ₁ →
        π = π') :
    (π_star : Measure (X × X))
      = (endpointLaw d).withDensity (fun z => ENNReal.ofReal (φhat0 z.1 * φ1 z.2)) := by
  rw [huniq π_star π_prod hfeas hopt hprodfeas hprodopt]
  exact hπprod

--------------------------------------------------------------------------------
-- §7  Fortet–IPF–Sinkhorn existence (CGP Theorem 8.1, discrete Schrödinger system)
--------------------------------------------------------------------------------

/-- **Fortet–IPF–Sinkhorn convergence / existence (CGP Theorem 8.1, (8.4a)–(8.4d)).**
For distributions `p, q` and a positive kernel `G = (g_{ij})`, there exist positive
vectors `φ(0,·), φ̂(0,·), φ(1,·), φ̂(1,·)` solving the discrete Schrödinger system
`φ(0,i)=Σⱼ g_{ij}φ(1,j)`, `φ̂(1,j)=Σᵢ g_{ij}φ̂(0,i)`, `φ(0,i)φ̂(0,i)=pᵢ`,
`φ(1,j)φ̂(1,j)=qⱼ`.  (Uniqueness holds up to the scaling `φ ↦ αφ`, `φ̂ ↦ φ̂/α`; the
matrix-scaling / Sinkhorn form of the Schrödinger system.)

Now a thin wrapper: the Schrödinger-bridge-free content is staged in
`ForMathlib.sinkhorn_potentials_exist`, which this delegates to. The mass-conservation
hypothesis `hsum : ∑ pᵢ = ∑ qⱼ` (necessary; implicit in the paper where `p, q` are
coupling marginals) is added there and threaded through here. -/
theorem sinkhorn_potentials_exist {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hsum : ∑ i, p i = ∑ j, q j)
    (G : ι → ι → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∃ φ0 φhat0 φ1 φhat1 : ι → ℝ,
      (∀ i, 0 < φ0 i) ∧ (∀ i, 0 < φhat0 i) ∧ (∀ j, 0 < φ1 j) ∧ (∀ j, 0 < φhat1 j) ∧
      (∀ i, φ0 i = ∑ j, G i j * φ1 j) ∧            -- (8.4a)
      (∀ j, φhat1 j = ∑ i, G i j * φhat0 i) ∧      -- (8.4b)
      (∀ i, φ0 i * φhat0 i = p i) ∧                -- (8.4c)
      (∀ j, φ1 j * φhat1 j = q j) :=               -- (8.4d)
  ForMathlib.sinkhorn_potentials_exist p q hp hq hsum G hG

end ChenGeorgiouPavon2021
