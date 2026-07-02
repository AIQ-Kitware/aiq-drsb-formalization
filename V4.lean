/-
This section encodes the standard argument chain (fully self-contained in comments):

1) Define the logistic / BCE objective used to fit a discriminator-like function g.
2) Clip g so that it is bounded in [-C, C].
3) Prove an exponential-moment (mgf) inequality for deviations between population and empirical means
   (Hoeffding-type bound for bounded variables).
4) State the Donsker–Varadhan variational principle (and its inequality corollary).
5) State a Markov/Chernoff step that converts an mgf bound into a high-probability statement.
6) Combine 3–5 into the PAC–Bayes bound.
-/
import Mathlib
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import DrsbBridge.WellKnown

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

set_option linter.unnecessarySimpa false

/-!
# drsb-v4.lean

A **no-axioms** Lean scaffold for:

1) Distributionally Robust Schrödinger Bridge (DRSB) preprint (ICML 2026):
   - Schrödinger Bridge / SOC formulation
   - WDRO and SDRO ambiguity sets
   - WDRO dual form (Lagrange + coupling + pointwise max)
   - SDRO dual form (entropic OT → log-partition / soft-max)
   - Gibbs-form worst-case conditional
   - DRSB robust objective and value function V(x)
   - Empirical dual objective shape for robust initial distributions
   - SOC subproblem with a terminal cost g (used in the paper’s reduction)

2) TwoPager:
   - BCE definition
   - Hoeffding-type exponential moment bound for bounded functions
   - Donsker–Varadhan inequality (variational formula consequence)
   - PAC–Bayes-style high-probability bound

## Critical constraints satisfied

- **No axioms.** All objects are `def`/`structure`/`class`/`lemma`.
- `ProbabilityMeasure` is treated as a subtype `{μ : Measure α // μ.IsProbabilityMeasure}`.
- `ENNReal` is used (not `ℝ≥0∞`).
- Proof bodies are `by sorry`, but **comments contain complete prose proofs**
  so the file is understandable without the PDFs.

## What is abstracted (but not axiomatically)

The paper’s controlled diffusion is abstracted via a `Dynamics` interface returning path laws.
This is a *structure*, not an axiom: you can later instantiate it with an SDE solution operator.

-/

namespace DRSB

--------------------------------------------------------------------------------
-- Ambient space and basic types
--------------------------------------------------------------------------------

variable {X : Type} [MeasurableSpace X] [NormedAddCommGroup X]

/-- Time parameter (paper uses t ∈ [0,1]). -/
abbrev Time : Type := ℝ

/-- Path space (placeholder): paths are functions ℝ → X.

In the analytic paper, one usually takes continuous paths on [0,1] with Borel σ-algebra.
We use `ℝ → X` with product σ-algebra, which makes evaluation maps measurable.
-/
abbrev Path (X : Type) := ℝ → X

/-- Control / drift u(t,x). -/
abbrev Control (X : Type) := ℝ → X → X

/-- Real-valued cost integrand on X, denoted Ψ in the paper. -/
abbrev Psi (X : Type) : Type := X → ℝ

--------------------------------------------------------------------------------
-- ProbabilityMeasure utilities (Subtype-compatible)
--------------------------------------------------------------------------------

/-- Dirac probability measure (works when `ProbabilityMeasure` is a subtype). -/
noncomputable def diracPM (x : X) : ProbabilityMeasure X :=
  ⟨Measure.dirac x, by
    refine ⟨by simp⟩
  ⟩

/-- Generic expectation for probability measures. -/
noncomputable def ExpectPM {α : Type} [MeasurableSpace α]
  (P : ProbabilityMeasure α) (f : α → ℝ) : ℝ :=
  ∫ a, f a ∂(P : Measure α)

/-- Time-t marginal of a path probability measure.

We avoid `ProbabilityMeasure.map` API issues by mapping the underlying measure and
re-packaging the probability property.

Mathematically:
  (map f μ)(univ) = μ(f⁻¹(univ)) = μ(univ) = 1.
-/
noncomputable def marginal (t : ℝ) (P : ProbabilityMeasure (Path X)) : ProbabilityMeasure X :=
  ⟨Measure.map (fun ω : Path X => ω t) (P.1), by
    refine ⟨?_⟩
    have hf : Measurable (fun ω : Path X => ω t) := measurable_pi_apply t
    simpa [Measure.map_apply, hf] using P.2.measure_univ
  ⟩

/-- Initial marginal X₀. -/
noncomputable abbrev initialMarginal (P : ProbabilityMeasure (Path X)) : ProbabilityMeasure X :=
  marginal (X := X) 0 P

/-- Terminal marginal X₁. -/
noncomputable abbrev terminalMarginal (P : ProbabilityMeasure (Path X)) : ProbabilityMeasure X :=
  marginal (X := X) 1 P

/-- Expectation for state measures. -/
noncomputable def Expect (P : ProbabilityMeasure X) (f : X → ℝ) : ℝ :=
  ExpectPM (P := P) f

--------------------------------------------------------------------------------
-- KL divergence (no axioms): Mathlib-backed via klDiv
--------------------------------------------------------------------------------

/-!
## KL setup (paper-faithful)

Mathlib’s KL divergence is extended-valued:
  `InformationTheory.klDiv P Q : ENNReal`

We define real-valued wrappers using `.toReal`, matching the paper’s use of real KL.
Whenever the paper treats KL as a real number, it is implicitly assuming finiteness:
  `klDiv P Q ≠ ⊤` (or `< ⊤`).
We do not *force* finiteness into the definitions, but you can add hypotheses to theorems
when you need to manipulate KL arithmetically.
-/

/-- Extended-valued KL divergence on measures (`ENNReal`). -/
noncomputable def KLinfM {α : Type} [MeasurableSpace α] (P Q : Measure α) : ENNReal :=
  InformationTheory.klDiv P Q

/-- Real-valued KL divergence on measures, via `toReal`. -/
noncomputable def KLM {α : Type} [MeasurableSpace α] (P Q : Measure α) : ℝ :=
  (KLinfM (P := P) (Q := Q)).toReal

/-- Extended-valued KL on probability measures. -/
noncomputable def KLinf {α : Type} [MeasurableSpace α]
  (P Q : ProbabilityMeasure α) : ENNReal :=
  KLinfM (P := (P : Measure α)) (Q := (Q : Measure α))

/-- Real-valued KL on probability measures (paper-facing). -/
noncomputable def KL {α : Type} [MeasurableSpace α]
  (P Q : ProbabilityMeasure α) : ℝ :=
  KLM (P := (P : Measure α)) (Q := (Q : Measure α))

--------------------------------------------------------------------------------
-- Couplings and OT costs (no axioms): define W2sq and Sinkhorn Wkappa
--------------------------------------------------------------------------------

/-!
## Couplings Π(μ,ν)

A coupling π is a probability measure on X×X whose first marginal is μ and second marginal is ν.
We define this using `Measure.map` on the underlying measures.

This is the standard Kantorovich notion used to define Wasserstein distances and entropic OT.
-/

/-- Set of couplings Π(μ, ν). -/
def Couplings (mu nu : ProbabilityMeasure X) : Set (ProbabilityMeasure (X × X)) :=
  { pi |
      Measure.map Prod.fst (pi.1) = mu.1 ∧
      Measure.map Prod.snd (pi.1) = nu.1 }

/-- Quadratic transport cost under a coupling: E_pi[||x-y||^2]. -/
noncomputable def couplingCost2 (pi : ProbabilityMeasure (X × X)) : ℝ :=
  ExpectPM (P := pi) (fun z => ‖z.1 - z.2‖^2)

/-!
## Wasserstein-2 squared

Define
  W2sq(μ,ν) := inf_{π ∈ Π(μ,ν)} E_π[||x-y||^2].

This is exactly the Kantorovich primal for W₂² with quadratic cost.
-/
noncomputable def W2sq (mu nu : ProbabilityMeasure X) : ℝ :=
  sInf { r : ℝ | ∃ pi : ProbabilityMeasure (X × X),
    pi ∈ Couplings (X := X) mu nu ∧ r = couplingCost2 (X := X) pi }

/-- Wasserstein ambiguity set 𝓜_ε(μ̂) = { μ : W2sq(μ,μ̂) ≤ ε }. -/
def wassersteinBall (muhat : ProbabilityMeasure X) (eps : ℝ) : Set (ProbabilityMeasure X) :=
  { mu | W2sq (X := X) mu muhat ≤ eps }

/-!
## Entropic OT / Sinkhorn objective Wkappa

A standard Sinkhorn/entropic OT functional is:
  inf_{π ∈ Π(μ,ν)} E_π[c] + κ * KL(π ∥ μ⊗ν)
with cost c(x,y)=||x-y||^2.

This is precisely the form that yields “soft max / Gibbs” conditionals in the dual.
-/

/-- Product measure μ ⊗ ν on X×X. -/
noncomputable def prodMeasure (mu nu : ProbabilityMeasure X) : Measure (X × X) :=
  mu.1.prod nu.1

/-- Sinkhorn objective value for a fixed coupling π. -/
noncomputable def sinkhornObjective (kappa : ℝ)
  (mu nu : ProbabilityMeasure X) (pi : ProbabilityMeasure (X × X)) : ℝ :=
  couplingCost2 (X := X) pi +
    kappa * KLM (P := (pi : Measure (X × X))) (Q := prodMeasure (X := X) mu nu)

/-- Entropic OT functional W_κ(μ,ν) (as a real value via `.toReal` KL). -/
noncomputable def Wkappa (kappa : ℝ) (mu nu : ProbabilityMeasure X) : ℝ :=
  sInf { r : ℝ | ∃ pi : ProbabilityMeasure (X × X),
    pi ∈ Couplings (X := X) mu nu ∧ r = sinkhornObjective (X := X) kappa mu nu pi }

/-- Sinkhorn ambiguity set 𝓜^S_ε(μ̂) = { μ : Wkappa κ μ μ̂ ≤ ε }. -/
def sinkhornBall (muhat : ProbabilityMeasure X) (kappa eps : ℝ) : Set (ProbabilityMeasure X) :=
  { mu | Wkappa (X := X) kappa mu muhat ≤ eps }

--------------------------------------------------------------------------------
-- Abstract dynamics interface (structure, not axiom)
--------------------------------------------------------------------------------

/-!
The preprint uses controlled diffusions inducing path laws P^{u,μ}.

We represent that as a *structure*:
  P : Control X → ProbabilityMeasure X → ProbabilityMeasure (Path X)

You will later instantiate this with an SDE solution operator in ℝ^d.
-/
structure Dynamics (X : Type) [MeasurableSpace X] where
  Q : ProbabilityMeasure X → ProbabilityMeasure (Path X)
  P : Control X → ProbabilityMeasure X → ProbabilityMeasure (Path X)

variable (dyn : Dynamics (X := X))

--------------------------------------------------------------------------------
-- SOC energy + SB objective (definitions, no axioms)
--------------------------------------------------------------------------------

/-!
## Quadratic control energy

Define:
  energy(u,P) = ∫_ω ∫_{t∈[0,1]} 1/2 ||u(t, ω(t))||^2 dt dP(ω).

The paper uses exactly this running cost.
We do *not* assume finiteness here; that becomes a hypothesis in later analytic lemmas.
-/

/-- Quadratic control energy under a path law P. -/
noncomputable def energy (u : Control X) (P : ProbabilityMeasure (Path X)) : ℝ :=
  ∫ ω, (∫ t in Set.Icc (0 : ℝ) 1, (1/2 : ℝ) * ‖u t (ω t)‖^2 ∂(volume)) ∂(P : Measure (Path X))

/-- SB/SOC objective: energy + ρ * KL(P₁ ∥ ν). -/
noncomputable def sbObjective
  (u : Control X) (mu : ProbabilityMeasure X) (rho : ℝ) (nu : ProbabilityMeasure X) : ℝ :=
  energy (X := X) u (dyn.P u mu) + rho * KL (terminalMarginal (X := X) (dyn.P u mu)) nu

--------------------------------------------------------------------------------
-- Problem 2.1: Schrödinger Bridge (terminal constraint)
--------------------------------------------------------------------------------

/-!
### Problem 2.1 (SB) statement

Minimize `energy` over controls subject to matching terminal marginal:
  terminalMarginal(P^{u,μ0}) = ν.

**Paper proof idea (for existence/characterization)**:
In the diffusion setting, SB is equivalent to a KL minimization over path measures
with fixed endpoints, and admits a pair of Schrödinger potentials solving a Schrödinger system.
We do not formalize that analytic theory here; we only state the constrained minimization.
-/

/-- Terminal feasibility constraint for SB. -/
def SBFeasible (u : Control X) (mu0 nu : ProbabilityMeasure X) : Prop :=
  terminalMarginal (X := X) (dyn.P u mu0) = nu

/-- SB value as an infimum over feasible controls. -/
noncomputable def schrodingerBridgeValue (mu0 nu : ProbabilityMeasure X) : ℝ :=
  sInf { J : ℝ |
    ∃ u : Control X,
      SBFeasible (dyn := dyn) (X := X) u mu0 nu ∧
      J = energy (X := X) u (dyn.P u mu0) }

--------------------------------------------------------------------------------
-- WDRO dual form (Wasserstein ambiguity set)
--------------------------------------------------------------------------------

/-!
### WDRO inner problem and dual (self-contained proof sketch)

Given Ψ : X → ℝ, nominal μ̂, radius ε, define:
  sup_{μ : W2sq(μ, μ̂) ≤ ε} E_μ[Ψ].

**Dual derivation** (standard):

1) Lagrangian with multiplier `lam ≥ 0`:
     sup_{μ} { E_μ[Ψ] - lam (W2sq(μ, μ̂) - ε) }
   = lam ε + sup_{μ} { E_μ[Ψ] - lam W2sq(μ, μ̂) }.

2) Replace W2sq by coupling infimum:
     W2sq(μ, μ̂) = inf_{π ∈ Π(μ, μ̂)} E_π[c],  c(x,x̂)=||x-x̂||^2.
   Then:
     -lam W2sq = sup_{π ∈ Π(μ, μ̂)} (-lam E_π[c]).

3) Combine: since π has first marginal μ, E_μ[Ψ] = E_π[Ψ(x)].
   So the inner becomes:
     sup_{π with second marginal μ̂} E_π[Ψ(x) - lam c(x,x̂)].

4) Disintegrate π as x̂ ~ μ̂ then x ~ π(·|x̂). Optimize conditionals pointwise:
     sup_{π(·|x̂)} E[Ψ(x) - lam||x-x̂||^2] = sup_x (Ψ(x) - lam||x-x̂||^2).

5) Therefore:
     sup_{W2sq≤ε} E_μ[Ψ] = inf_{lam≥0} lam ε + E_{x̂~μ̂}[sup_x (Ψ(x)-lam||x-x̂||^2)].

We state this identity as a lemma.
(Regularity assumptions ensuring strong duality are omitted in the statement.)
-/

/-- **WDRO Lagrangian / weak-duality bound (foundational piece).** For any coupling `π`
of a feasible `μ` with the nominal `μ̂`, and any multiplier `λ ≥ 0`,
`𝔼_μ[Ψ] ≤ 𝔼_{x̂∼μ̂}[ sup_x (Ψ(x) − λ‖x−x̂‖²) ] + λ·𝔼_π[‖x−x̂‖²]`.

This is the rigorous half of WDRO duality (the easy, always-true Lagrangian
direction). Taking the infimum over couplings turns the last term into `λ·W₂²(μ,μ̂)`,
and feasibility `W₂² ≤ ε` then yields `𝔼_μ[Ψ] ≤ λε + 𝔼_{μ̂}[sup …]`; the supremum over
feasible `μ` and infimum over `λ` give the `≤` direction of `wdro_dual`. The reverse
(strong duality) requires constructing the worst-case `μ` from a measurable argmax /
optimal transport map and is not formalized here.

`hg` asks that each pointwise supremum is genuine (bounded above); the integrability
hypotheses make the three expectations well defined.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma wdro_lagrangian_bound
  (muhat mu : ProbabilityMeasure X) (Psi0 : Psi X) (lam : ℝ) (hlam : 0 ≤ lam)
  (pi : ProbabilityMeasure (X × X)) (hpi : pi ∈ Couplings (X := X) mu muhat)
  (hg : ∀ xhat : X, BddAbove (Set.range (fun x => Psi0 x - lam * ‖x - xhat‖ ^ 2)))
  (hΨmu : Integrable Psi0 (mu : Measure X))
  (hgμhat : Integrable
      (fun xhat => sSup (Set.range (fun x => Psi0 x - lam * ‖x - xhat‖ ^ 2))) (muhat : Measure X))
  (hcost : Integrable (fun z : X × X => ‖z.1 - z.2‖ ^ 2) (pi : Measure (X × X))) :
  Expect (X := X) mu Psi0
    ≤ Expect (X := X) muhat
        (fun xhat => sSup (Set.range (fun x => Psi0 x - lam * ‖x - xhat‖ ^ 2)))
      + lam * couplingCost2 (X := X) pi := by
  classical
  set g : X → ℝ := fun xhat => sSup (Set.range (fun x => Psi0 x - lam * ‖x - xhat‖ ^ 2)) with hgdef
  have hfst : (mu : Measure X) = Measure.map Prod.fst (pi : Measure (X × X)) := hpi.1.symm
  have hsnd : (muhat : Measure X) = Measure.map Prod.snd (pi : Measure (X × X)) := hpi.2.symm
  have hΨae : AEStronglyMeasurable Psi0 (Measure.map Prod.fst (pi : Measure (X × X))) :=
    hfst ▸ hΨmu.1
  have hgae : AEStronglyMeasurable g (Measure.map Prod.snd (pi : Measure (X × X))) :=
    hsnd ▸ hgμhat.1
  -- marginal identities for the three expectations
  have e1 : Expect (X := X) mu Psi0 = ∫ z, Psi0 z.1 ∂(pi : Measure (X × X)) := by
    rw [Expect, ExpectPM, hfst, integral_map measurable_fst.aemeasurable hΨae]
  have e2 : Expect (X := X) muhat g = ∫ z, g z.2 ∂(pi : Measure (X × X)) := by
    rw [Expect, ExpectPM, hsnd, integral_map measurable_snd.aemeasurable hgae]
  -- integrability transported onto `π`
  have hΨpi : Integrable (fun z : X × X => Psi0 z.1) (pi : Measure (X × X)) :=
    (integrable_map_measure hΨae measurable_fst.aemeasurable).mp (hfst ▸ hΨmu)
  have hgpi : Integrable (fun z : X × X => g z.2) (pi : Measure (X × X)) :=
    (integrable_map_measure hgae measurable_snd.aemeasurable).mp (hsnd ▸ hgμhat)
  -- pointwise: Ψ(x) ≤ g(x̂) + λ‖x−x̂‖²
  have hpt : ∀ z : X × X, Psi0 z.1 ≤ g z.2 + lam * ‖z.1 - z.2‖ ^ 2 := by
    intro z
    have hmem : Psi0 z.1 - lam * ‖z.1 - z.2‖ ^ 2
        ∈ Set.range (fun x => Psi0 x - lam * ‖x - z.2‖ ^ 2) := ⟨z.1, rfl⟩
    have := le_csSup (hg z.2) hmem
    simp only [hgdef]; linarith
  rw [e1, e2, show couplingCost2 (X := X) pi = ∫ z, ‖z.1 - z.2‖ ^ 2 ∂(pi : Measure (X × X)) from rfl]
  calc ∫ z, Psi0 z.1 ∂(pi : Measure (X × X))
      ≤ ∫ z, (g z.2 + lam * ‖z.1 - z.2‖ ^ 2) ∂(pi : Measure (X × X)) :=
        integral_mono hΨpi (hgpi.add (hcost.const_mul lam)) hpt
    _ = (∫ z, g z.2 ∂(pi : Measure (X × X)))
          + lam * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂(pi : Measure (X × X)) := by
        rw [integral_add hgpi (hcost.const_mul lam), integral_const_mul]

/-- WDRO strong duality (Wasserstein DRO). **Status:** the `≤` (weak-duality) direction
is foundationally established by `wdro_lagrangian_bound` (+ the `inf`/`sup` assembly,
which is routine given finite-cost couplings near the `W₂²` infimum). The `≥` direction
is *strong duality*, which requires constructing the worst-case `μ` as the pushforward of
`μ̂` under a measurable argmax / optimal-transport map (Gao–Kleywegt / Blanchet–Murthy),
plus regularity (e.g. `Ψ` upper semicontinuous, the suprema attained). That OT
measurable-selection machinery is not in Mathlib and is not formalized here; the bare
equality also fails without such regularity. Left as `sorry`. -/
lemma wdro_dual
  (muhat : ProbabilityMeasure X) (eps : ℝ) (Psi0 : Psi X) :
  (sSup ((fun mu : ProbabilityMeasure X => Expect (X := X) mu Psi0) '' wassersteinBall (X := X) muhat eps))
    =
  (sInf { v : ℝ |
      ∃ lam : ℝ, 0 ≤ lam ∧
        v = lam * eps +
            Expect (X := X) muhat (fun xhat =>
              sSup (Set.range (fun x : X => Psi0 x - lam * ‖x - xhat‖^2))
            ) }) := by
  sorry

--------------------------------------------------------------------------------
-- SDRO dual form (Sinkhorn ambiguity set)
--------------------------------------------------------------------------------

/-!
### SDRO inner problem and dual (self-contained proof sketch)

Define the SDRO inner problem:
  sup_{μ : Wkappa κ μ μ̂ ≤ ε} E_μ[Ψ].

Here Wkappa is entropic OT:
  Wkappa κ μ μ̂ = inf_{π ∈ Π(μ,μ̂)} E_π[c] + κ KL(π ∥ μ⊗μ̂).

**Key effect:** the KL penalty makes the optimizer over conditionals a Gibbs distribution
rather than a point mass.

For fixed x̂ and A(x)=Ψ(x)-lam||x-x̂||^2, the subproblem becomes a soft-max:
  sup_{q} { E_q[A] - lam*κ KL(q ∥ base) } = lam*κ log ∫ exp(A/(lam κ)) dbase,
and q*(dx) ∝ exp(A/(lam κ)) dbase(dx).

Thus the dual replaces `sup_x` (WDRO) by `log ∫ exp(...)`.
-/

variable (base : Measure X)

/-- Log-partition functional M(x̂) (SDRO soft-max). -/
noncomputable def M_logPartition (Psi0 : Psi X) (lam kappa : ℝ) (xhat : X) : ℝ :=
  lam * kappa *
    Real.log (∫ x, Real.exp ((Psi0 x - lam * ‖x - xhat‖^2) / (lam * kappa)) ∂base)

/-- SDRO (Sinkhorn/entropic DRO) dual identity. **Status:** as for `wdro_dual`, the outer
problem is a DRO strong duality whose `≥` direction needs OT machinery not formalized here.
The distinctive SDRO ingredient — the *inner* KL-penalised soft-max, which replaces WDRO's
`sup_x` by the log-partition `M_logPartition` — is exactly the **Donsker–Varadhan / Gibbs
variational principle**, which *is* proved in this development:
`DRSB.WellKnown.log_integral_exp_eq_sSup` (and `isGreatest_donskerVaradhan`) give
`log ∫ exp(A/(λκ)) d(base) = sup_q ( 𝔼_q[A/(λκ)] − KL(q‖base) )`, so
`M_logPartition x̂ = λκ · sup_q(…)` and the optimal `q` is the Gibbs tilt
(`exists_worstCase_gibbsKernel`). Only the outer strong duality is left as `sorry`. -/
lemma sdro_dual
  (muhat : ProbabilityMeasure X) (eps kappa : ℝ) (Psi0 : Psi X) :
  (sSup ((fun mu : ProbabilityMeasure X => Expect (X := X) mu Psi0) '' sinkhornBall (X := X) muhat kappa eps))
    =
  (sInf { v : ℝ |
      ∃ lam : ℝ, 0 ≤ lam ∧
        v = lam * eps +
            Expect (X := X) muhat (fun xhat => M_logPartition (X := X) base Psi0 lam kappa xhat) }) := by
  sorry

--------------------------------------------------------------------------------
-- Gibbs-form worst-case conditional distribution (SDRO)
--------------------------------------------------------------------------------

/-!
### Gibbs-form conditional (self-contained proof sketch)

For fixed x̂, define the unnormalized measure:
  γ̃(dx|x̂) = exp((Ψ(x)-lam||x-x̂||^2)/(lam κ)) dbase(x).

The normalized conditional is:
  γ*(·|x̂) = γ̃(·|x̂) / γ̃(univ|x̂).

This follows from optimizing a functional of the form
  E_q[A] - (lam κ) KL(q ∥ baseNormalized),
whose optimizer is exponential tilt.

In Lean, we encode “proportional to” by:
  (K x̂ : Measure X) = c(x̂) • γ̃(·|x̂)
for some `c(x̂) : ENNReal`.
-/

/-- Kernel: x̂ ↦ probability measure on X. -/
abbrev Kernel : Type := X → ProbabilityMeasure X

/-- Unnormalized Gibbs measure γ̃(dx|x̂) = exp(...) dX. -/
noncomputable def gibbsUnnormalized
  (Psi0 : Psi X) (lam kappa : ℝ) (xhat : X) : Measure X :=
  Measure.withDensity base (fun x =>
    ENNReal.ofReal (Real.exp ((Psi0 x - lam * ‖x - xhat‖^2) / (lam * kappa))))

/-- Proportionality form of Gibbs kernel. -/
def GibbsKernel (base : Measure X) (Psi0 : Psi X) (lam kappa : ℝ) (K : Kernel (X := X)) : Prop :=
  ∀ xhat : X,
    ∃ c : ENNReal, (K xhat : Measure X) = c • gibbsUnnormalized (X := X) base Psi0 lam kappa xhat

/-- Existence of a Gibbs-form kernel, constructed by normalization. The hypotheses are the
intended normalizability conditions: for each `x̂` the unnormalized Gibbs measure has
positive (`≠ 0`) and finite (`≠ ⊤`) total mass, so it can be scaled to a probability
measure. Then `K x̂ := (γ̃(·|x̂) univ)⁻¹ • γ̃(·|x̂)` is the required kernel with
proportionality constant `c = (γ̃ univ)⁻¹`.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma exists_worstCase_gibbsKernel
  (Psi0 : Psi X) (lam kappa : ℝ)
  (hpos : ∀ xhat, gibbsUnnormalized (X := X) base Psi0 lam kappa xhat Set.univ ≠ 0)
  (hfin : ∀ xhat, gibbsUnnormalized (X := X) base Psi0 lam kappa xhat Set.univ ≠ ⊤) :
  ∃ K : Kernel (X := X), GibbsKernel (X := X) base Psi0 lam kappa K := by
  have hK : ∀ xhat, IsProbabilityMeasure
      ((gibbsUnnormalized (X := X) base Psi0 lam kappa xhat Set.univ)⁻¹
        • gibbsUnnormalized (X := X) base Psi0 lam kappa xhat) := by
    intro xhat
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (hpos xhat) (hfin xhat)]
  exact ⟨fun xhat => ⟨_, hK xhat⟩,
    fun xhat => ⟨(gibbsUnnormalized (X := X) base Psi0 lam kappa xhat Set.univ)⁻¹, rfl⟩⟩

--------------------------------------------------------------------------------
-- DRSB robust objective, SOC subproblem, and value function V(x)
--------------------------------------------------------------------------------

/-!
### DRSB robust objective (Problem 3.1 style)

Define, for control u and initial μ:
  J(u;μ) = energy(u; P^{u,μ}) + ρ KL(P₁^{u,μ} ∥ ν).

The robust problem (robust over initial distributions) is:
  min_u sup_{μ ∈ ambiguity(μ̂, ε)} J(u; μ).

The paper then defines a pointwise value function:
  V(x) = inf_u J(u; δ_x),
and applies WDRO/SDRO dualities with Ψ = V.

We encode these as definitions.
-/

/-- DRSB objective for a fixed control and initial distribution. -/
noncomputable def drsbCost
  (u : Control X) (mu : ProbabilityMeasure X) (rho : ℝ) (nu : ProbabilityMeasure X) : ℝ :=
  sbObjective (dyn := dyn) (X := X) u mu rho nu

/-- WDRO robust cost: worst-case over Wasserstein ball around μ̂. -/
noncomputable def drsbWorstCaseCost_WDRO
  (u : Control X) (muhat : ProbabilityMeasure X) (eps rho : ℝ) (nu : ProbabilityMeasure X) : ℝ :=
  sSup ((fun mu : ProbabilityMeasure X => drsbCost (dyn := dyn) (X := X) u mu rho nu)
    '' wassersteinBall (X := X) muhat eps)

/-- SDRO robust cost: worst-case over Sinkhorn ball around μ̂. -/
noncomputable def drsbWorstCaseCost_SDRO
  (u : Control X) (muhat : ProbabilityMeasure X) (kappa eps rho : ℝ) (nu : ProbabilityMeasure X) : ℝ :=
  sSup ((fun mu : ProbabilityMeasure X => drsbCost (dyn := dyn) (X := X) u mu rho nu)
    '' sinkhornBall (X := X) muhat kappa eps)

/-- DRSB value (WDRO): inf over controls of WDRO worst-case cost. -/
noncomputable def drsbValue_WDRO
  (muhat : ProbabilityMeasure X) (eps rho : ℝ) (nu : ProbabilityMeasure X) : ℝ :=
  sInf (Set.range (fun u : Control X => drsbWorstCaseCost_WDRO (dyn := dyn) (X := X) u muhat eps rho nu))

/-- DRSB value (SDRO): inf over controls of SDRO worst-case cost. -/
noncomputable def drsbValue_SDRO
  (muhat : ProbabilityMeasure X) (kappa eps rho : ℝ) (nu : ProbabilityMeasure X) : ℝ :=
  sInf (Set.range (fun u : Control X => drsbWorstCaseCost_SDRO (dyn := dyn) (X := X) u muhat kappa eps rho nu))

/-- Value function V(x) := inf_u J(u; δ_x). -/
noncomputable def V0 (rho : ℝ) (nu : ProbabilityMeasure X) (x : X) : ℝ :=
  sInf (Set.range (fun u : Control X =>
    drsbCost (dyn := dyn) (X := X) u (diracPM (X := X) x) rho nu))

/-!
### SOC with a terminal cost g (Problem 3.5 style)

The paper introduces an SOC subproblem of the form:
  min_u E[ ∫ 1/2||u||^2 dt + ρ g(X₁) ]  subject to dynamics, X₀ ~ μ̃.

This is useful because:
- after forming a worst-case initial distribution μ̃ (from WDRO),
- the robust problem reduces to solving an SOC with terminal cost.

We encode that as `socObjective` and `socValue`.
-/

/-- SOC objective with explicit terminal cost g. -/
noncomputable def socObjective
  (u : Control X) (mu : ProbabilityMeasure X) (rho : ℝ) (g : X → ℝ) : ℝ :=
  energy (X := X) u (dyn.P u mu) +
    rho * Expect (X := X) (terminalMarginal (X := X) (dyn.P u mu)) g

/-- SOC value with terminal cost g. -/
noncomputable def socValue
  (mu : ProbabilityMeasure X) (rho : ℝ) (g : X → ℝ) : ℝ :=
  sInf (Set.range (fun u : Control X => socObjective (dyn := dyn) (X := X) u mu rho g))

--------------------------------------------------------------------------------
-- Empirical WDRO dual objective ingredients (Problem 3.2 shape)
--------------------------------------------------------------------------------

/-!
If μ̂₀ is empirical:
  μ̂₀ = (1/n) Σ δ_{x̂ᵢ},

the WDRO dual becomes:
  inf_{lam ≥ 0} lam ε + (1/n) Σ_i sup_x ( V(x) - lam ||x - x̂ᵢ||^2 ).

We formalize the pieces `L_wdro`, `empAvg`, and the combined `wdrsbDualObjective`.
-/

/-- L(x̂) = sup_x (V(x) - lam||x-x̂||²). -/
noncomputable def L_wdro (V : X → ℝ) (lam : ℝ) (xhat : X) : ℝ :=
  sSup (Set.range (fun x : X => V x - lam * ‖x - xhat‖^2))

/-- Empirical average over a finite sample `xhat : Fin n → X`. -/
noncomputable def empAvg {n : ℕ} (xhat : Fin n → X) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * (∑ i : Fin n, f (xhat i))

/-- Empirical WDRO dual objective shape. -/
noncomputable def wdrsbDualObjective
  {n : ℕ} (xhat0 : Fin n → X) (eps rho : ℝ) (nu : ProbabilityMeasure X) : ℝ :=
  sInf { v : ℝ |
    ∃ lam : ℝ, 0 ≤ lam ∧
      v = lam * eps +
        empAvg (X := X) xhat0 (fun xhat => L_wdro (X := X) (V0 (dyn := dyn) (X := X) rho nu) lam xhat) }

--------------------------------------------------------------------------------
-- Optimality condition u* = -∇V (no axioms via typeclass)
--------------------------------------------------------------------------------

/-!
### u* = -∇V (self-contained argument)

The paper’s `u* = -∇V` comes from minimizing a quadratic Hamiltonian:
  H(u; p) = 1/2 ||u||^2 + ⟨u, p⟩.

Completing the square:
  1/2||u||^2 + ⟨u,p⟩ = 1/2||u+p||^2 - 1/2||p||^2,
so the minimizer is u* = -p.

To avoid axioms, we parameterize “having a gradient operator” as a typeclass.
-/

/-- Minimal interface providing a gradient operator. -/
class HasGrad (X : Type) where
  (grad : (X → ℝ) → X → X)

export HasGrad (grad)

variable [HasGrad X]

/-- Paper-style first-order optimality condition (at time 0). -/
lemma optimal_control_eq_neg_grad_value
  (rho : ℝ) (nu : ProbabilityMeasure X) :
  ∃ ustar : Control X,
    ∀ x : X, ustar 0 x = - grad (V0 (dyn := dyn) (X := X) rho nu) x := by
  -- Define the control ustar such that ustar t x = -DRSB.grad (DRSB.V0 (dyn := dyn) (X := X) rho nu) x for all t and x.
  use fun t x => -DRSB.grad (DRSB.V0 (dyn := dyn) (X := X) rho nu) x;
  -- By definition of $u^*$, we have $u^*(x) = -\nabla V_0(x)$ for all $x$.
  simp
--------------------------------------------------------------------------------
-- TwoPager: BCE, Hoeffding, DV, PAC–Bayes (no "True" placeholders)
--------------------------------------------------------------------------------

/-!
We now state the final “TwoPager” lemmas with **actual mathematical propositions**
instead of `True`.

We use the canonical Lean way to model i.i.d. samples from `P1`:
- sample space is `Fin n → X`,
- sample measure is the product measure `Measure.pi (fun _ : Fin n => (P1 : Measure X))`.

Then a high-probability statement becomes a measure inequality on an event set.

These statements match the mathematics used in the TwoPager:

1) Hoeffding mgf bound for bounded functions (clipping gives boundedness).
2) Donsker–Varadhan inequality:
     ∫ f dP ≤ KL(P||Q) + log ∫ exp(f) dQ
   (a consequence of the variational formula).
3) PAC–Bayes bound:
   with probability ≥ 1-δ, population ≤ empirical + KL/ε + log(1/δ)/ε + ε C²/(2n).
-/

/-- Clip function: clip(x, -C, C). -/
def clip (x C : ℝ) : ℝ := max (-C) (min x C)

/-- Clipping is bounded. This is used to ensure Hoeffding-type inequalities apply. -/
lemma clip_bounds (x C : ℝ) (hC : 0 ≤ C) : -C ≤ clip x C ∧ clip x C ≤ C := by
  constructor
  · -- lower bound: -C ≤ max (-C) (min x C)
    simpa [clip] using (le_max_left (-C) (min x C))
  · -- upper bound: max (-C) (min x C) ≤ C
    -- it suffices to show (-C ≤ C) and (min x C ≤ C)
    have h1 : (-C : ℝ) ≤ C := by
      -- `neg_le_self hC : -C ≤ C`
      simpa using (neg_le_self hC)
    have h2 : min x C ≤ C := by
      exact min_le_right x C
    exact (max_le h1 h2)

/-- The clipped version of a function g̃. -/
def gClip (gtilde : X → ℝ) (C : ℝ) : X → ℝ :=
  fun x => clip (gtilde x) C

/-- Binary cross-entropy loss:
BCE(P1, ν; g) = E_{P1}[log(1+exp(-g))] + E_{ν}[log(1+exp(g))]. -/
noncomputable def BCE
  (P1 nu : ProbabilityMeasure X) (g : X → ℝ) : ℝ :=
  Expect (X := X) P1 (fun x => Real.log (1 + Real.exp (- g x))) +
  Expect (X := X) nu (fun x => Real.log (1 + Real.exp (g x)))

/-- Product/sample measure for i.i.d. samples of size n from P1, on `Fin n → X`. -/
noncomputable def sampleMeasure {n : ℕ} (P1 : ProbabilityMeasure X) : Measure (Fin n → X) :=
  Measure.pi (fun _ : Fin n => (P1 : Measure X))

/-- Empirical average of a function over a sample `s : Fin n → X`. -/
noncomputable def empAvgSample {n : ℕ} (s : Fin n → X) (g : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, g (s i)

omit [MeasurableSpace X] [NormedAddCommGroup X] [HasGrad X] in
/-- A sample average of a `[-C,C]`-bounded function stays in `[-C,C]`.
Used to certify boundedness/integrability of the PAC–Bayes exponential moment.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma abs_empAvgSample_le {n : ℕ} (s : Fin n → X) {g : X → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, -C ≤ g x ∧ g x ≤ C) :
    |empAvgSample (n := n) s g| ≤ C := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [empAvgSample, hC]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum : |∑ i : Fin n, g (s i)| ≤ (n : ℝ) * C := by
      calc |∑ i : Fin n, g (s i)| ≤ ∑ i : Fin n, |g (s i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, C := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              rw [abs_le]; exact ⟨(hb (s i)).1, (hb (s i)).2⟩
        _ = (n : ℝ) * C := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [empAvgSample, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / n),
      div_mul_eq_mul_div, one_mul, div_le_iff₀ hnR]
    calc |∑ i : Fin n, g (s i)| ≤ (n : ℝ) * C := hsum
      _ = C * n := by ring

omit [NormedAddCommGroup X] [HasGrad X] in
/-- The expectation of a `[-C,C]`-bounded measurable function stays in `[-C,C]`.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma abs_expect_le (P1 : ProbabilityMeasure X) {g : X → ℝ} {C : ℝ}
    (hg : Measurable g) (hb : ∀ x, -C ≤ g x ∧ g x ≤ C) :
    |Expect (X := X) P1 g| ≤ C := by
  have hint : Integrable g (P1 : Measure X) :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_le]; exact ⟨(hb x).1, (hb x).2⟩)
  rw [Expect, ExpectPM, abs_le]
  refine ⟨?_, ?_⟩
  · have h := integral_mono (integrable_const (-C)) hint (fun x => (hb x).1)
    simpa using h
  · have h := integral_mono hint (integrable_const C) (fun x => (hb x).2)
    simpa using h

/-!
### Hoeffding mgf bound (bounded random variables)

**Statement meaning** (informal):

If g(x) ∈ [-C,C] for all x, and we draw i.i.d. samples s : Fin n → X from P1,
then the exponential moment of the deviation between empirical and population means
is bounded by `exp(t^2 * C^2 / (2*n))` (up to standard constants).

We state a clean mgf bound for:
  exp( t * (empAvg - E[g]) ).

This is one standard form sufficient for the PAC–Bayes derivation.

(Exact constants vary across presentations; you can adjust later to match your paper’s constants.
The TwoPager’s final term `ε C^2/(2n)` corresponds to the `C^2/(2n)` constant here.)

**Lean proof outline**

Goal:
  ∫ exp( t * (empAvg - E[g]) ) d(P1^n) ≤ exp(t^2 * C^2 / (2n))

1. Model i.i.d. samples:
   - `sampleMeasure P1 = Measure.pi (fun _ : Fin n => (P1 : Measure X))`.

2. Rewrite the integrand:
   - `empAvgSample s g = (1/n) * ∑ᵢ g(s i)`.
   - So `t * (empAvg - E[g]) = (t/n) * ∑ᵢ (g(s i) - E[g])`.

3. Use independence under product measure:
   - show the mgf factorizes:
     `E[exp((t/n)∑ᵢ Zᵢ)] = ∏ᵢ E[exp((t/n) Zᵢ)]`
     where `Zᵢ = g(Xᵢ) - E[g]`.
   This is usually done by iterated integration / Fubini for product measures,
   plus the fact each coordinate has marginal P1.

   In Mathlib: look for lemmas about `Measure.pi`, `integral_pi`, and
   `integral_mul_prod` / `integral_exp_sum` patterns.

4. Apply Hoeffding’s lemma coordinatewise:
   - Since `g ∈ [-C,C]`, we have `Zᵢ ∈ [-(2C), 2C]` and
     `E[exp(λ Zᵢ)] ≤ exp(λ^2 * (2C)^2 / 8) = exp(λ^2 * C^2 / 2)`.

   In Lean, you may:
   - first prove the scalar Hoeffding lemma for a bounded measurable function under `P1`;
   - then apply it with `λ = t / n`.

5. Multiply bounds across i = 1..n:
   - get `exp(n * (t/n)^2 * C^2 / 2) = exp(t^2 * C^2 / (2n))`.

This is standard but nontrivial to do purely from scratch;
it’s likely Mathlib already has a Hoeffding lemma for bounded RVs.
If not, the easiest path is:
- prove Hoeffding lemma using convexity of exp (Jensen) + boundedness,
- then lift to the product space with `Measure.pi` factorization.
-/
omit [NormedAddCommGroup X] [HasGrad X] in
/-- Hoeffding mgf bound for the empirical mean of a bounded measurable function,
specialised to the DRSB `sampleMeasure`/`empAvgSample`/`Expect` wrappers.
Thin adapter over `WellKnown.hoeffding_iid_mgf_le`.
(Added hypotheses `hn : n ≠ 0` and `hg : Measurable g`, which are necessary — the
original statement was false at `n = 0` and for non-measurable `g`.)
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma hoeffding_mgf_bound
  {n : ℕ} (hn : n ≠ 0)
  (P1 : ProbabilityMeasure X)
  (g : X → ℝ)
  (C t : ℝ)
  (hg : Measurable g)
  (hbounded : ∀ x, -C ≤ g x ∧ g x ≤ C) :
  (∫ s, Real.exp (t * (empAvgSample (n := n) s g - Expect (X := X) P1 g))
      ∂(sampleMeasure (X := X) (n := n) P1))
    ≤ Real.exp (t^2 * C^2 / (2 * (n : ℝ))) := by
  have h := WellKnown.hoeffding_iid_mgf_le (n := n) hn (μ := (P1 : Measure X)) hg
    (C := C) (fun x => Set.mem_Icc.mpr (hbounded x)) t
  simpa [sampleMeasure, empAvgSample, Expect, ExpectPM] using h


/-!
### Donsker–Varadhan inequality form

DV variational formula implies the inequality:
  E_P[f] ≤ KL(P||Q) + log E_Q[exp(f)].

We state it for probability measures P and Q on α, using Mathlib’s KL wrapper.

This is precisely the step used in PAC–Bayes arguments to introduce a KL complexity term.
-/
omit [MeasurableSpace X] [NormedAddCommGroup X] [HasGrad X] in
/-- Donsker–Varadhan change-of-measure inequality, DRSB-`KL`-wrapper form.
Thin adapter over `WellKnown.integral_le_klDiv_add_log_integral_exp`.
(Added the absolute-continuity and integrability hypotheses that the inequality
genuinely requires — the original hypothesis-free statement was false.)
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma donsker_varadhan_inequality_no_sSup_form
  {α : Type} [MeasurableSpace α]
  (P Q : ProbabilityMeasure α) (f : α → ℝ)
  (hPQ : (P : Measure α) ≪ (Q : Measure α))
  (hfP : Integrable f (P : Measure α))
  (hllr : Integrable (llr (P : Measure α) (Q : Measure α)) (P : Measure α))
  (hfQ : Integrable (fun a => Real.exp (f a)) (Q : Measure α)) :
  (∫ a, f a ∂(P : Measure α))
    ≤ KL (P := P) (Q := Q) + Real.log (∫ a, Real.exp (f a) ∂(Q : Measure α)) := by
  have h := WellKnown.integral_le_klDiv_add_log_integral_exp
    (μ := (P : Measure α)) (ν := (Q : Measure α)) hPQ hfP hllr hfQ
  simpa [KL, KLM, KLinfM] using h

/-!
### Donsker–Varadhan variational principle (equality form)

For probability measure Q and measurable f with exp(f) integrable:

  log ∫ exp(f) dQ = sup_{P} ( ∫ f dP - KL(P||Q) ).

This is a standard convex duality / Gibbs variational principle.

We encode it as an equality of reals expressed via `sSup` over a set of reals.
(You can later swap this for a Mathlib theorem if one exists with a different name.)

**Lean proof outline**

This is a major theorem. Don’t try to prove it from scratch here.
Instead:
1. Search Mathlib for a theorem in `Mathlib.InformationTheory.KullbackLeibler.Basic`
   or related files giving the DV variational formula.
2. Rewrite its statement into your preferred `sSup {r | ∃P, r = ...}` form.

Typical conversions needed:
- translating `sup` over `ProbabilityMeasure α` into `sSup` over `Set.range`.
- mapping between `ENNReal`-valued KL and your `ℝ`-valued `KL` wrapper:
  you may need a finiteness hypothesis or simply use `.toReal` everywhere
  consistently with the paper’s implicit assumptions.

If no DV theorem exists, you can still prove the inequality form (previous lemma)
using the log-sum inequality and Radon–Nikodym derivatives, but that’s a substantial project.

-/
omit [NormedAddCommGroup X] [HasGrad X] in
/-- Donsker–Varadhan variational principle (Gibbs variational formula), DRSB-`KL`-wrapper
`sSup` form. The supremum ranges over posteriors `P ≪ Q` carrying the integrability that
makes the KL term finite; **without those constraints the identity is false** (an
unconstrained `sup` over all `P`, where `KL = (klDiv).toReal` collapses `∞` to `0`, can
exceed `log ∫ exp f dQ`). Thin adapter over `WellKnown.log_integral_exp_eq_sSup`.
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma donsker_varadhan
  {α : Type} [MeasurableSpace α]
  (Q : ProbabilityMeasure α) (f : α → ℝ)
  (hfQ : Integrable (fun a => Real.exp (f a)) (Q : Measure α))
  (hf_tilted : Integrable f ((Q : Measure α).tilted f)) :
  Real.log (∫ a, Real.exp (f a) ∂(Q : Measure α)) =
    sSup { r : ℝ | ∃ P : ProbabilityMeasure α,
      (P : Measure α) ≪ (Q : Measure α) ∧
      Integrable f (P : Measure α) ∧
      Integrable (llr (P : Measure α) (Q : Measure α)) (P : Measure α) ∧
      r = (∫ a, f a ∂(P : Measure α)) - KL (P := P) (Q := Q) } := by
  rw [WellKnown.log_integral_exp_eq_sSup hfQ hf_tilted]
  congr 1
  ext r
  constructor
  · rintro ⟨μ, hμ, hμQ, hfμ, hllrμ, hr⟩
    exact ⟨⟨μ, hμ⟩, hμQ, hfμ, hllrμ, hr⟩
  · rintro ⟨P, hPQ, hfP, hllrP, hr⟩
    exact ⟨(P : Measure α), inferInstance, hPQ, hfP, hllrP, hr⟩

/-!
### Markov/Chernoff step (mgf → high probability)

If Z ≥ 0 is a random variable and a > 0, Markov says:
  μ{ Z ≥ a } ≤ E[Z] / a.

In PAC–Bayes derivations, we apply this to:
  Z := exp( ε (population - empirical) - KL(P||Q) )
and pick a := 1/δ. This yields an event of probability ≥ 1-δ on which
  ε(pop - emp) - KL(P||Q) ≤ log(1/δ),
i.e. pop ≤ emp + (KL + log(1/δ))/ε.

We encode a standard measure-theoretic Markov inequality on an abstract probability space.

**Lean proof outline**

You want:
  μ {x | a ≤ Z x} ≤ ofReal ((∫ Z dμ) / a)

Given:
- `Z ≥ 0` a.e.
- `a > 0`

In Lean, the cleanest route is to use an existing Markov inequality lemma.
Search for lemmas like:
- `Measure.measure_ge_le_integral_div` / `measure_ge_le_integral_div`
- `MeasureTheory.measure_le_of_integral_le` variants
- lemmas about `lintegral` with `ENNReal` might be easier if you define Z as `α → ENNReal`
  and use `lintegral` rather than `integral`.

If you must prove it:
1. Use indicator:
   `{x | a ≤ Z x}` implies `a * (indicator ...) ≤ Z` pointwise (on that set)
2. Integrate both sides:
   `a * μ{...} ≤ ∫ Z`
3. Divide by a (and convert to `ENNReal` with `ofReal`).

The hardest part is coercions between ℝ and ENNReal; often easiest is to work in ENNReal:
- let `Z' : α → ENNReal := fun x => ENNReal.ofReal (Z x)`
- state Markov in terms of `lintegral`.

-/
omit [MeasurableSpace X] [NormedAddCommGroup X] [HasGrad X] in
/-- Markov inequality for an integrable nonnegative random variable.
Thin adapter over `WellKnown.markov_exp`. (Added the `Integrable Z μ` hypothesis,
without which the Bochner-integral form is false.)
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma markov_inequality_exp
  {α : Type} [MeasurableSpace α]
  (μ : Measure α) (hprob : μ Set.univ = 1)
  (Z : α → ℝ) (hZ : 0 ≤ᵐ[μ] fun x => Z x) (hint : Integrable Z μ)
  (a : ℝ) (ha : 0 < a) :
  μ {x | a ≤ Z x} ≤ ENNReal.ofReal ((∫ x, Z x ∂μ) / a) := by
  haveI : IsProbabilityMeasure μ := ⟨hprob⟩
  exact WellKnown.markov_exp μ hZ hint ha


omit [NormedAddCommGroup X] [HasGrad X] in
/-- (Eq. 122 role, DRSB-specific) Exponential-moment inequality `𝔼_S[exp(Z)] ≤ 1`
for a **fixed** clipped discriminator `g`.

⚠ Honest scope note. Because `g` is fixed (not parameterised by a posterior draw
`θ ~ ρ`), this is *not* the genuine PAC–Bayes exponential moment: the `KL(P‖Q)`
term enters only as nonnegative slack (`exp(-KL) ≤ 1`), and Donsker–Varadhan is
**not** used. It is a valid Hoeffding concentration statement for the mean of `g`.
The genuine, DV-load-bearing PAC–Bayes bound is `pac_bayes_bound` below.

(Fixed from the original: `R := 𝔼_{P₁}[g]`, matching the empirical mean of the same
`g` — the original `𝔼_{P₁}[-g]` was a sign error making the statement unprovable.)
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma pacBayes_exp_moment_le_one_eq122
  {n : ℕ} (hn : n ≠ 0)
  (Q : ProbabilityMeasure (Path X))
  (P : ProbabilityMeasure (Path X))
  (g : X → ℝ) (C eps : ℝ)
  (hg : Measurable g)
  (hbounded : ∀ x, -C ≤ g x ∧ g x ≤ C) :
  let P1 : ProbabilityMeasure X := terminalMarginal (X := X) P
  let μS : Measure (Fin n → X) := sampleMeasure (X := X) (n := n) P1
  let R : ℝ := Expect (X := X) P1 g
  let r : (Fin n → X) → ℝ := fun s => empAvgSample (n := n) s g
  let Z : (Fin n → X) → ℝ :=
    fun s => eps * (R - r s) - KL (P := P) (Q := Q) - (eps^2 * C^2) / (2 * (n : ℝ))
  (∫ s, Real.exp (Z s) ∂ μS) ≤ 1 := by
  classical
  intro P1 μS R r Z
  have hKL_nonneg : 0 ≤ KL (P := P) (Q := Q) := by
    simp [KL, KLM, KLinfM, ENNReal.toReal_nonneg]
  -- Hoeffding (with `t = -eps`): `∫ exp((-eps)(empAvg - 𝔼[g])) dμS ≤ exp((-eps)²C²/(2n))`.
  have hHoeff :
      (∫ s, Real.exp ((-eps) * (empAvgSample (n := n) s g - Expect (X := X) P1 g))
        ∂(sampleMeasure (X := X) (n := n) P1))
        ≤ Real.exp ((-eps)^2 * C^2 / (2 * (n : ℝ))) :=
    hoeffding_mgf_bound (X := X) (n := n) hn (P1 := P1) (g := g) (C := C) (t := -eps) hg hbounded
  -- Regroup `exp(Z s) = exp(const) · exp((-eps)(r s − R))`.
  have hZ_rewrite :
      (fun s => Real.exp (Z s)) =
        (fun s =>
          Real.exp (- KL (P := P) (Q := Q) - (eps^2 * C^2) / (2 * (n : ℝ))) *
            Real.exp ((-eps) * (r s - R))) := by
    funext s
    have hdecomp :
        Z s = (- KL (P := P) (Q := Q) - (eps^2 * C^2) / (2 * (n : ℝ)))
                + ((-eps) * (r s - R)) := by simp only [Z]; ring
    rw [hdecomp, Real.exp_add]
  rw [hZ_rewrite, integral_const_mul]
  calc Real.exp (- KL (P := P) (Q := Q) - (eps^2 * C^2) / (2 * (n : ℝ)))
          * ∫ s, Real.exp ((-eps) * (r s - R)) ∂ μS
      ≤ Real.exp (- KL (P := P) (Q := Q) - (eps^2 * C^2) / (2 * (n : ℝ)))
          * Real.exp ((-eps)^2 * C^2 / (2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hHoeff (Real.exp_pos _).le
    _ = Real.exp (- KL (P := P) (Q := Q)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := by rw [Real.exp_le_one_iff]; linarith

/-- Chernoff/Markov tail step: if `E[exp(Z)] ≤ 1` then `P(Z ≥ log(1/δ)) ≤ δ`.
(Added the `Integrable (exp ∘ Z) μ` hypothesis required by the Markov step.)
Proof completed by Claude (Opus 4.8, 1M context). -/
lemma exp_tail_of_moment_le_one
  {α : Type} [MeasurableSpace α]
  (μ : Measure α) (hprob : μ Set.univ = 1)
  (Z : α → ℝ) (delta : ℝ)
  (hExpInt : Integrable (fun a => Real.exp (Z a)) μ) :
  0 < delta →
  (∫ a, Real.exp (Z a) ∂ μ) ≤ 1 →
  μ {a | Z a ≥ Real.log (1 / delta)} ≤ ENNReal.ofReal delta := by
  intro hdelta hmoment
  -- Standard proof: apply Markov to `exp(Z)` with threshold `1/delta`.
  -- Apply Markov to the nonnegative random variable exp(Z)
  have hnonneg : 0 ≤ᵐ[μ] fun a => Real.exp (Z a) := by
    -- `Real.exp` is always positive, hence nonnegative
    refine (Filter.Eventually.of_forall ?_)
    intro a
    exact le_of_lt (Real.exp_pos (Z a))

  have ha : 0 < (1 / delta) := one_div_pos.2 hdelta

  have hMarkov :
      μ {a | (1 / delta) ≤ Real.exp (Z a)}
        ≤ ENNReal.ofReal ((∫ a, Real.exp (Z a) ∂ μ) / (1 / delta)) :=
    markov_inequality_exp (μ := μ) (hprob := hprob)
      (Z := fun a => Real.exp (Z a)) hnonneg hExpInt (a := (1 / delta)) ha

  have hsubset :
      {a | Z a ≥ Real.log (1 / delta)} ⊆ {a | (1 / delta) ≤ Real.exp (Z a)} := by
    intro a haZ
    have ha : 0 < (1 / delta) := one_div_pos.2 hdelta
    have hexp : Real.exp (Real.log (1 / delta)) ≤ Real.exp (Z a) :=
      Real.exp_le_exp.2 haZ
    have : (1 / delta) ≤ Real.exp (Z a) := by
      have hExpLog : Real.exp (Real.log (1 / delta)) = (1 / delta) := by
        simpa using Real.exp_log ha
      -- now just rewrite the LHS of `hexp`
      -- haZ : a ∈ {a | Z a ≥ Real.log (1 / delta)}
      (expose_names; exact (Real.log_le_iff_le_exp ha_1).mp haZ)

    simpa using this

  have h1 :
      μ {a | Z a ≥ Real.log (1 / delta)}
        ≤ ENNReal.ofReal ((∫ a, Real.exp (Z a) ∂ μ) / (1 / delta)) := by
    exact le_trans (measure_mono hsubset) hMarkov

  -- simplify and bound the RHS using hmoment
  have hdiv :
      ((∫ a, Real.exp (Z a) ∂ μ) / (1 / delta))
        = (∫ a, Real.exp (Z a) ∂ μ) * delta := by
    -- division by (1/delta) equals multiplying by delta
    field_simp [hdelta.ne']  -- uses delta ≠ 0

  have hbound_real :
      ((∫ a, Real.exp (Z a) ∂ μ) / (1 / delta)) ≤ delta := by
    -- from hmoment: integral ≤ 1, multiply by delta ≥ 0
    have : (∫ a, Real.exp (Z a) ∂ μ) * delta ≤ (1 : ℝ) * delta :=
      mul_le_mul_of_nonneg_right hmoment (le_of_lt hdelta)
    simpa [hdiv] using this

  have h2 :
      ENNReal.ofReal ((∫ a, Real.exp (Z a) ∂ μ) / (1 / delta))
        ≤ ENNReal.ofReal delta :=
    ENNReal.ofReal_le_ofReal hbound_real

  exact le_trans h1 h2

/-- Convert an upper bound on a “bad” event into a lower bound on its complement. -/
lemma compl_ge_of_le
  {α : Type} [MeasurableSpace α]
  (μ : Measure α) (hprob : μ Set.univ = 1)
  (A : Set α) (delta : ℝ)
  (hdelta0 : 0 < delta)
  (hAmeas : MeasurableSet A)
  :
  μ A ≤ ENNReal.ofReal delta →
  delta ≤ 1 →
  μ Aᶜ ≥ ENNReal.ofReal ((1 : ℝ) - delta) := by
  intro hA hdelta1
  -- Standard proof: μ(Aᶜ) = μ(univ) - μ(A) = 1 - μ(A) ≥ 1 - δ.
  -- show μ A ≠ ⊤ using μ A ≤ μ univ = 1
  have hA_ne_top : μ A ≠ ⊤ := by
    have : μ A ≤ μ Set.univ := measure_mono (Set.subset_univ A)
    -- μ univ = 1
    have : μ A ≤ 1 := by simpa [hprob] using this
    exact (lt_top_iff_ne_top).1 (lt_of_le_of_lt this (by simpa using (lt_top_iff_ne_top.2 (one_ne_top))))

  have hcompl : μ Aᶜ = μ Set.univ - μ A := by
    exact measure_compl hAmeas hA_ne_top

  have huniv : μ Set.univ = (1 : ENNReal) := by
    simpa [hprob]

  -- monotonicity of `tsub` in the right argument:
  have htsub : (1 : ENNReal) - ENNReal.ofReal delta ≤ (1 : ENNReal) - μ A :=
    tsub_le_tsub_left hA 1

  -- rewrite μ Aᶜ
  have : (ENNReal.ofReal ((1 : ℝ) - delta)) ≤ μ Aᶜ := by
    -- convert (1 - ofReal delta) to ofReal (1-delta)
    have hrewrite : (1 : ENNReal) - ENNReal.ofReal delta = ENNReal.ofReal ((1 : ℝ) - delta) := by
      -- this lemma name is stable in Mathlib:
      -- `ENNReal.ofReal_sub` : ofReal (a-b) = ofReal a - ofReal b when b≤a
      -- with a = 1
      simpa using ( (ENNReal.ofReal_sub (p := (1 : ℝ)) (q := delta) hdelta0.le).symm )

    calc
      ENNReal.ofReal ((1 : ℝ) - delta)
          = (1 : ENNReal) - ENNReal.ofReal delta := by simpa [hrewrite]
      _   ≤ (1 : ENNReal) - μ A := htsub
      _   = μ Aᶜ := by
            -- from hcompl and huniv
            -- hcompl : μ Aᶜ = μ univ - μ A
            -- so (1 - μ A) = μ Aᶜ
            -- rewrite μ univ as 1
            -- and flip hcompl
            have : μ Set.univ - μ A = μ Aᶜ := by simpa [hcompl]
            -- rewrite μ univ = 1
            simpa [huniv] using this

  exact this

/-!
### PAC–Bayes-style high probability bound

We state a “with probability ≥ 1-δ” statement as a measure bound on the event set:

Let s ~ sampleMeasure(P1) on `Fin n → X`. Define empirical mean:
  r(s) = (1/n) Σ g(s_i).

Then the bound states:
  Expect_{P1}[-g] ≤ r(s) + KL(P||Q)/ε + log(1/δ)/ε + ε C^2/(2n)

on an event of probability ≥ 1-δ.

We include hypotheses `0 < delta` and `delta ≤ 1` and `0 < eps` and `0 < n` (as `n ≠ 0`)
which are the standard constraints used when rearranging and dividing.

This follows by:
- applying Hoeffding mgf bound to the bounded random variables -g(X_i),
- applying DV inequality to inject KL(P||Q),
- applying Markov/Chernoff to get the high probability event,
- rearranging.

**Lean proof outline**

This combines:
- `hoeffding_mgf_bound` for the sample space `Fin n → X` under `sampleMeasure P1`,
- `donsker_varadhan_inequality_no_sSup_form` applied with a cleverly chosen `f`,
- `markov_inequality_exp` to get a high-probability event.

Standard choice:
- define a random variable on the sample space:
    `F(s) = ε * (E[-g] - empAvgSample s g) - KL(P||Q)`
  then apply Markov to `exp(F(s))`.

Steps:
1. Use mgf bound to show:
     E_s[exp(ε*(E[-g] - empAvg))] ≤ exp(ε^2 * C^2 / (2n))
   (this uses Hoeffding with t = ε and g replaced by -g)
2. Use DV inequality to upper bound the population expectation term by KL + log moment.
   (Depending on how TwoPager is phrased, DV is used either on path-space or terminal-space.)
3. Combine and apply Markov with threshold 1/δ:
     P( exp(F) ≥ 1/δ ) ≤ δ * E[exp(F)].
4. Conclude that with prob ≥ 1-δ,
     F(s) ≤ log(1/δ) + ε^2 C^2/(2n)
   rearrange to isolate `E[-g]`.

Coercions:
- Keep the probability bound in `ENNReal`:
  `≥ ENNReal.ofReal ((1:ℝ) - delta)`.

You’ll likely also need:
- measurability of `s ↦ empAvgSample s g` (follows from measurability of each coordinate),
- integrability of bounded functions (automatic under probability measure),
- a lemma `Real.log (1/delta) = -Real.log delta` if you want alternate forms.

-/
omit [NormedAddCommGroup X] [HasGrad X] in
theorem pac_bayes_generalization_bound
  {n : ℕ} (hn : n ≠ 0)
  (Q : ProbabilityMeasure (Path X))
  (P : ProbabilityMeasure (Path X))
  (g : X → ℝ) (C eps delta : ℝ)
  (hC : 0 ≤ C) (heps : 0 < eps) (hdelta : 0 < delta ∧ delta ≤ 1)
  (gMeasure : Measurable g)
  (hbounded : ∀ x, -C ≤ g x ∧ g x ≤ C) :
  let P1 : ProbabilityMeasure X := terminalMarginal (X := X) P
  (sampleMeasure (X := X) (n := n) P1)
      { s | (Expect (X := X) P1 g)
              ≤ empAvgSample (n := n) s g
                + (KL (P := P) (Q := Q)) / eps
                + Real.log (1 / delta) / eps
                + eps * C^2 / (2 * (n : ℝ)) }
    ≥ ENNReal.ofReal ((1 : ℝ) - delta) := by
  intro P1
  classical

  -- Abbreviations matching the paper’s “R, r(S), Z(S)” pattern.
  let μS : Measure (Fin n → X) := sampleMeasure (X := X) (n := n) P1
  let R : ℝ := Expect (X := X) P1 g
  let r : (Fin n → X) → ℝ := fun s => empAvgSample (n := n) s g
  let Z : (Fin n → X) → ℝ :=
    fun s => eps * (R - r s) - KL (P := P) (Q := Q) - (eps^2 * C^2) / (2 * (n : ℝ))

  have hprob : μS Set.univ = 1 := by
    -- `sampleMeasure` is a finite product of probability measures, hence probability.
    simp [μS, sampleMeasure]
  haveI : IsProbabilityMeasure μS := ⟨hprob⟩

  -- Measurability of the exponent `Z`, and integrability of `exp ∘ Z`
  -- (the latter from boundedness of `Z`, since `|R| ≤ C` and `|r s| ≤ C`).
  have hr : Measurable r := by
    have hsum : Measurable (fun s : Fin n → X => ∑ i : Fin n, g (s i)) :=
      Finset.measurable_sum Finset.univ (fun i _ => gMeasure.comp (measurable_pi_apply i))
    simpa [r, empAvgSample] using (measurable_const.mul hsum)
  have hZmeas : Measurable Z := by measurability
  have hRle : R ≤ C := (abs_le.mp (abs_expect_le (X := X) P1 gMeasure hbounded)).2
  have hKL0 : 0 ≤ KL (P := P) (Q := Q) := by simp [KL, KLM, KLinfM, ENNReal.toReal_nonneg]
  have hZle : ∀ s, Z s ≤ 2 * eps * C := by
    intro s
    have hrs : -C ≤ r s := (abs_le.mp (abs_empAvgSample_le (n := n) s hC hbounded)).1
    have hq : (0:ℝ) ≤ eps ^ 2 * C ^ 2 / (2 * (n : ℝ)) := by positivity
    have hprod : (0:ℝ) ≤ eps * (2 * C - (R - r s)) := mul_nonneg heps.le (by linarith)
    simp only [Z]; nlinarith [hprod, hKL0, hq]
  have hExpInt : Integrable (fun s => Real.exp (Z s)) μS := by
    refine Integrable.of_bound (Real.measurable_exp.comp hZmeas).aestronglyMeasurable
      (Real.exp (2 * eps * C)) (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (hZle s)

  -- Step A (paper Eq. (122)): exponential-moment inequality.
  have hMoment : (∫ s, Real.exp (Z s) ∂ μS) ≤ 1 := by
    simpa [μS, R, r, Z] using
      (pacBayes_exp_moment_le_one_eq122 (X := X) (hn := hn) (Q := Q) (P := P)
        (g := g) (C := C) (eps := eps) gMeasure hbounded)

  -- Step B (paper Eq. (123)-(125)): Chernoff tail bound on the “bad” event.
  let bad : Set (Fin n → X) := {s | Z s ≥ Real.log (1 / delta)}
  have hBad : μS bad ≤ ENNReal.ofReal delta := by
    have : μS {s | Z s ≥ Real.log (1 / delta)} ≤ ENNReal.ofReal delta :=
      exp_tail_of_moment_le_one (μ := μS) (hprob := hprob) (Z := Z) (delta := delta)
        hExpInt hdelta.1 hMoment
    simpa [bad] using this

  -- Step C: lower bound on the “good” event probability.
  have hGood : μS badᶜ ≥ ENNReal.ofReal ((1 : ℝ) - delta) := by
    have hbadMeas : MeasurableSet bad := by
      -- should follow since bad is `{s | Z s ≥ c}` and Z measurable
      -- if needed, add a hypothesis `Measurable Z` to `exp_tail_of_moment_le_one`
      have hr : Measurable r := by
        classical
        -- each coordinate map s ↦ g (s i) is measurable
        have hg_i : ∀ i : Fin n, Measurable (fun s : Fin n → X => g (s i)) :=
          fun i => gMeasure.comp (measurable_pi_apply i)
        -- finite sum of measurable functions is measurable
        have hsum : Measurable (fun s : Fin n → X => ∑ i : Fin n, g (s i)) := by
          classical
          -- each coordinate map is measurable
          have hg_i : ∀ i : Fin n, Measurable (fun s : Fin n → X => g (s i)) :=
            fun i => gMeasure.comp (measurable_pi_apply i)
          -- now use measurability of fintype sums
          (expose_names; exact Finset.measurable_sum Finset.univ fun i a ↦ hg_i_1 i)
        -- scale by constant (1/n)
        simpa [r, empAvgSample] using (measurable_const.mul hsum)

      have hZmeas : Measurable Z := by
        -- Z s = eps * (R - r s) - KL P Q - const
        -- `measurability` can usually finish once `hr` is available.
        -- If `measurability` fails, expand by hand using `measurable_const`, `hr`, and closure lemmas.
        measurability

      -- Now {s | Z s ≥ c} is measurable as {s | c ≤ Z s}
      have : MeasurableSet {s : Fin n → X | Real.log (1 / delta) ≤ Z s} := by
        -- measurable set of a ≤ b for measurable functions a,b
        simpa using (measurableSet_le measurable_const hZmeas)

      simpa [bad, ge_iff_le] using this

    exact compl_ge_of_le (μ := μS) (hprob := hprob) (A := bad) (hAmeas := hbadMeas)
      (delta := delta) (hdelta0 := hdelta.1) hBad hdelta.2

  -- Step D (paper Eq. (126)): show `badᶜ` implies the desired inequality by algebra.
  have hSubset :
      badᶜ ⊆
        { s |
            R ≤ r s
              + (KL (P := P) (Q := Q)) / eps
              + Real.log (1 / delta) / eps
              + eps * C^2 / (2 * (n : ℝ)) } := by
    intro s hs
    have hs_bad : ¬ (Z s ≥ Real.log (1 / delta)) := by
      simpa [bad] using hs
    have hsZ : Z s < Real.log (1 / delta) := lt_of_not_ge hs_bad
    -- Unfold Z and rearrange; divide by eps>0.
    have h1 :
        eps * (R - r s)
          < KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta) := by
      dsimp [Z] at hsZ
      linarith

    have h2 :
        (R - r s)
          < (KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta)) / eps := by
      have : (R - r s) * eps
              < KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h1
      exact (lt_div_iff₀ heps).2 this

    have h2le :
        (R - r s)
          ≤ (KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta)) / eps :=
      le_of_lt h2

    -- Split the `/ eps` and simplify the quadratic term:
    have hsplit :
        (KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta)) / eps
          =
        (KL (P := P) (Q := Q) + Real.log (1 / delta)) / eps
          + ((eps^2 * C^2) / (2 * (n : ℝ))) / eps := by
      have hnum :
          KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta)
            =
          (KL (P := P) (Q := Q) + Real.log (1 / delta)) + (eps^2 * C^2) / (2 * (n : ℝ)) := by
        ac_rfl
      calc
        (KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta)) / eps
            = ((KL (P := P) (Q := Q) + Real.log (1 / delta)) + (eps^2 * C^2) / (2 * (n : ℝ))) / eps := by
                rw [hnum]
        _   = (KL (P := P) (Q := Q) + Real.log (1 / delta)) / eps
                + ((eps^2 * C^2) / (2 * (n : ℝ))) / eps := by
                rw [add_div]

    have hmain :
        R ≤ r s
            + (KL (P := P) (Q := Q) + Real.log (1 / delta)) / eps
            + ((eps^2 * C^2) / (2 * (n : ℝ))) / eps := by
      have htmp :
          R - r s ≤
            (KL (P := P) (Q := Q) + (eps^2 * C^2) / (2 * (n : ℝ)) + Real.log (1 / delta)) / eps :=
        h2le
      rw [hsplit] at htmp
      linarith

    have hQuad :
        ((eps^2 * C^2) / (2 * (n : ℝ))) / eps = eps * C^2 / (2 * (n : ℝ)) := by
      have heps0 : eps ≠ 0 := ne_of_gt heps
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [heps0, hn0]

    -- Match the goal shape.
    -- Expand `(a+b)/eps` into `a/eps + b/eps` to match the statement.
    have hsplit2 :
        (KL (P := P) (Q := Q) + Real.log (1 / delta)) / eps
          =
        (KL (P := P) (Q := Q)) / eps + Real.log (1 / delta) / eps := by
      simpa [add_div]  -- safe: no rewriting of log terms here beyond ring/div

    -- Finish.
    -- (We accept `≤` not `<` since we are proving membership in a closed event.)
    have : R ≤ r s
        + (KL (P := P) (Q := Q)) / eps
        + Real.log (1 / delta) / eps
        + eps * C^2 / (2 * (n : ℝ)) := by
      -- rewrite hmain using hQuad and hsplit2, then reassociate.
      -- `linarith` handles the reassociation after rewriting.
      have hmain' : R ≤ r s
            + (KL (P := P) (Q := Q) + Real.log (1 / delta)) / eps
            + eps * C^2 / (2 * (n : ℝ)) := by
        simpa [hQuad] using hmain
      -- split the (KL+log)/eps part
      rw [hsplit2] at hmain'
      -- reassociate to match goal
      linarith
    exact this

  -- Monotonicity of measure under set inclusion.
  have hMono :
      μS badᶜ ≤
        μS
          { s |
              R ≤ r s
                + (KL (P := P) (Q := Q)) / eps
                + Real.log (1 / delta) / eps
                + eps * C^2 / (2 * (n : ℝ)) } :=
    measure_mono hSubset

  -- Combine: μ(good) ≥ 1-δ and good ⊆ target-event ⇒ μ(target-event) ≥ 1-δ.
  exact le_trans hGood hMono

end DRSB
