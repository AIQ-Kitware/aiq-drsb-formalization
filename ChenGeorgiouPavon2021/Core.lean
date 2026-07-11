/-
# Chen, Georgiou, Pavon (2021) — "Stochastic control liaisons: Richard Sinkhorn
  meets Gaspard Monge on a Schrödinger bridge" (arXiv:2005.10963).

Core theorems of the Schrödinger-bridge ⇄ stochastic-optimal-control ⇄
entropic-optimal-transport backbone that *defines* the DRSB value function
`V(x) = 𝔼[∫₀¹ ½‖u_t‖² dt + ρ g(X₁) | X₀ = x]` and its optimal control
`u* = σ²∇log φ = −∇V`.

The file provides the common finite and algebraic definitions used by the CGP development.
The Gaussian, sequence, and Wiener-dyadic layers are concrete; continuum SDE and PDE inputs that
are not yet constructed in Lean remain explicit interfaces.

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
import ForMathlib.MeasureTheory.GaussianCameronMartin
import ForMathlib.MeasureTheory.WienerMeasure
import ForMathlib.MeasureTheory.KLDataProcessing
import ForMathlib.MeasureTheory.KLChainRule

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

--------------------------------------------------------------------------------
-- Ambient space and basic path/control types
--------------------------------------------------------------------------------

variable {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Provisional ambient path carrier: functions `ℝ → X`. In CGP the path space is
`C([0,1];ℝⁿ)`. Continuum results should migrate to the anchored continuous interval-path type
once its measurable and topological API is complete. -/
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

end ChenGeorgiouPavon2021
