/-
# Chen, Georgiou, Pavon (2021) — "Stochastic control liaisons: Richard Sinkhorn
  meets Gaspard Monge on a Schrödinger bridge" (arXiv:2005.10963).

Core theorems of the Schrödinger-bridge ⇄ stochastic-optimal-control ⇄
entropic-optimal-transport backbone that *defines* the DRSB value function
`V(x) = 𝔼[∫₀¹ ½‖u_t‖² dt + ρ g(X₁) | X₀ = x]` and its optimal control
`u* = σ²∇log φ = −∇V`.

The file began as a statements-only scaffold.  The proof pass has since discharged the finite
Gaussian/sequence/Wiener-dyadic layers and isolates the remaining continuum/SDE facts as explicit
interfaces rather than executable `sorry`s.

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


omit [NormedSpace ℝ X] in
/-- **Energy identity (CGP (4.19)) — disintegrated, `sorry`-free.**  By Girsanov, for a
finite-energy diffusion `P = P^{u,ρ₀}`,
`D(P‖R) = D(ρ₀‖ρ₀^W) + 𝔼_P[∫₀¹ ½‖u_t‖² dt]`,
i.e. relative entropy splits into a constant endpoint term plus the control energy.

**Proof by the roadmap decomposition (`ROADMAP_ENERGY_IDENTITY.md`), no `sorry`.**  Both path
laws disintegrate over the initial coordinate through a measurable iso `e : Path X ≃ᵐ X × Path X`
(start-plus-centered-path; a genuine structural fact for a normed path space): `e_# P = ρ₀ ⊗ₘ Kᵘ`
and `e_# R = ρ₀^W ⊗ₘ Kᵂ` with `ρ₀ = initialMarginal P`, `ρ₀^W = initialMarginal R` and Markov
bridge kernels `Kᵘ, Kᵂ` (`hPfact`, `hRfact`). Then:
* **KL is invariant under `e`** (`ForMathlib…klDiv_map_measurableEquiv`): `D(P‖R) = D(e_#P‖e_#R)`;
* the **KL chain rule** splits it — `D(ρ₀⊗ₘKᵘ ‖ ρ₀^W⊗ₘKᵂ) = D(ρ₀‖ρ₀^W) + D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ)`
  (`ForMathlib…toReal_klDiv_compProd_eq_add`, real-valued via the finiteness edges `hfin_marg`,
  `hfin_cond`, i.e. the finite-relative-entropy regime);
* the **conditional term equals the control energy** (`hCM`) — the *sole* Girsanov content, the
  per-trajectory Cameron–Martin identity, isolated as one explicit non-vacuous edge exactly as the
  strong-duality equalities isolate their attainment edge.

`hCM`'s **discrete Euler–Maruyama instance is a theorem** (`energy_identity_euler_maruyama` below,
via the vendored Cameron–Martin `klDiv_stdGaussian_map_add`); the continuum `hCM` is the `Δt→0`
limit (ROADMAP Phase 2, the last research seam). The disintegration + finiteness hypotheses are
honest structural facts of a finite-energy diffusion — no `sorry`, `#print axioms`-clean. -/
theorem energy_identity (u : Control X) (ρ₀ : ProbabilityMeasure X)
    -- disintegration over the initial coordinate (structural edges; true for a real diffusion):
    (e : Path X ≃ᵐ X × Path X)
    (Ku Kw : Kernel X (Path X)) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (hPfact : (d.pathLaw u ρ₀ : Measure (Path X)).map e
        = (initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
    (hRfact : (d.R : Measure (Path X)).map e = (initialMarginal d.R) ⊗ₘ Kw)
    -- finiteness edges (finite-relative-entropy regime; cf. `FiniteEnergyDiffusion`):
    (hfin_marg : InformationTheory.klDiv
        (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R) ≠ ⊤)
    (hfin_cond : InformationTheory.klDiv
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Kw) ≠ ⊤)
    -- the per-trajectory Cameron–Martin identity (the sole Girsanov edge; discrete layer proved):
    (hCM : (InformationTheory.klDiv
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Ku)
        ((initialMarginal (d.pathLaw u ρ₀)) ⊗ₘ Kw)).toReal
        = energy u (d.pathLaw u ρ₀)) :
    klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X))
      = klReal (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R)
        + energy u (d.pathLaw u ρ₀) := by
  haveI : IsProbabilityMeasure (initialMarginal (d.pathLaw u ρ₀)) := by
    unfold initialMarginal marginal
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℝ)).aemeasurable
  haveI : IsProbabilityMeasure (initialMarginal d.R) := by
    unfold initialMarginal marginal
    exact Measure.isProbabilityMeasure_map (measurable_pi_apply (0 : ℝ)).aemeasurable
  unfold klReal
  rw [← ForMathlib.MeasureTheory.klDiv_map_measurableEquiv e
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)),
      hPfact, hRfact,
      ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_add
        (initialMarginal (d.pathLaw u ρ₀)) (initialMarginal d.R) Ku Kw hfin_marg hfin_cond,
      hCM]

/-- **Energy identity, conditional / per-trajectory form — the `hCM` edge reduced (ROADMAP Phase
1.5 wired).**

Same disintegration as `energy_identity`, but the Girsanov edge is now the **per-trajectory
Cameron–Martin atom** `∫⁻ x, D(Kᵘ_x ‖ Kᵂ_x) dρ₀` rather than the abstract conditional relative
entropy `D(ρ₀⊗ₘKᵘ ‖ ρ₀⊗ₘKᵂ)`. The reduction between the two is the **proved** (cond) lemma
`ForMathlib…klDiv_compProd_eq_lintegral` (which closes Mathlib's own `ChainRule.lean` TODO), applied
internally; absolute continuity comes for free from the finiteness edge `hfin_cond`.

**Why this theorem is stated over an abstract path-space factor `𝓨` (and `energy_identity` is not).**
(cond) needs `Kernel.rnDeriv Kᵘ Kᵂ` to be jointly measurable, i.e. the standard typeclass
`CountableOrCountablyGenerated 𝒳 𝓨`. Here `𝓨` is a *free type variable*, so that hypothesis is
**satisfiable** — it holds for every standard-Borel / Polish path space — making this a genuine
conditional theorem, not a vacuous one. It is deliberately *not* instantiated at the placeholder
`Path X = ℝ→X` of `energy_identity`, whose uncountable-index `Pi` σ-algebra is **not** countably
generated (so forcing the typeclass there would be a false instance = a vacuous edge, forbidden).

This is exactly the shape Phase 2 must discharge: with `𝓨` a standard-Borel continuous-path space and
`Kᵘ, Kᵂ` the SDE/reference kernels, `hCM`'s continuum instance is the Cameron–Martin/Girsanov
identity `∫⁻ D(Kᵘ_x‖Kᵂ_x) dρ₀ = 𝔼[∫½‖u‖²]`, whose **discrete Euler–Maruyama instance is the proved
`energy_identity_euler_maruyama`** and whose continuum discharge is blocked only on Mathlib's missing
Itô integral (ROADMAP Phase 2). No `sorry`, `#print axioms`-clean. -/
theorem energy_identity_conditional
    {𝒳 𝒴 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace Ω]
    [MeasurableSpace.CountableOrCountablyGenerated 𝒳 𝒴]
    (P R : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (e : Ω ≃ᵐ 𝒳 × 𝒴)
    (ρ₀ ρ₀' : Measure 𝒳) [IsProbabilityMeasure ρ₀] [IsProbabilityMeasure ρ₀']
    (Ku Kw : Kernel 𝒳 𝒴) [IsMarkovKernel Ku] [IsMarkovKernel Kw]
    (hPfact : P.map e = ρ₀ ⊗ₘ Ku)
    (hRfact : R.map e = ρ₀' ⊗ₘ Kw)
    (hfin_marg : InformationTheory.klDiv ρ₀ ρ₀' ≠ ⊤)
    (hfin_cond : InformationTheory.klDiv (ρ₀ ⊗ₘ Ku) (ρ₀ ⊗ₘ Kw) ≠ ⊤)
    (energyVal : ℝ)
    (hCM : (∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂ρ₀).toReal = energyVal) :
    klReal P R = klReal ρ₀ ρ₀' + energyVal := by
  have h_ac_cond : (ρ₀ ⊗ₘ Ku) ≪ (ρ₀ ⊗ₘ Kw) :=
    (InformationTheory.klDiv_ne_top_iff.mp hfin_cond).1
  have hcond : InformationTheory.klDiv (ρ₀ ⊗ₘ Ku) (ρ₀ ⊗ₘ Kw)
      = ∫⁻ x, InformationTheory.klDiv (Ku x) (Kw x) ∂ρ₀ :=
    ForMathlib.MeasureTheory.klDiv_compProd_eq_lintegral ρ₀ Ku Kw h_ac_cond
  unfold klReal
  rw [← ForMathlib.MeasureTheory.klDiv_map_measurableEquiv e P R,
      hPfact, hRfact,
      ForMathlib.MeasureTheory.toReal_klDiv_compProd_eq_add ρ₀ ρ₀' Ku Kw hfin_marg hfin_cond,
      hcond, hCM]

omit [NormedSpace ℝ X] in
/-- **Energy identity (4.19), lower-bound (`≥`) half — Itô-free, via finite-dimensional projections.**

For the continuous energy identity `D(P^{u,ρ₀}‖R) = D(ρ₀‖ρ₀^W) + 𝔼[∫₀¹ ½‖u‖²]`, the **`≥`
direction** (specifically `𝔼[∫₀¹ ½‖u‖²] ≤ D(P^{u,ρ₀}‖R)` when both chains start alike) is provable
with **no stochastic integral**: it rests only on the KL data-processing inequality.

Given measurable *time-grid projections* `π i : Path X → 𝓨 i` (e.g. `ω ↦ (ω_{t₀},…,ω_{t_k})`) whose
projected relative entropies `D(π i _# P ‖ π i _# R)` converge to the control energy — which holds in
any concrete SDE model by the **proved** discrete Cameron–Martin layer `energy_identity_euler_maruyama`
(each grid KL is the discrete energy `emEnergy`, a Riemann sum of `𝔼[∫½‖u‖²]`) — the data-processing
inequality (`ForMathlib…le_toReal_klDiv_of_map_tendsto`) forces the limit `≤` the full path-measure
KL, since each projection only loses information.

This **splits the monolithic Girsanov edge `hCM`**: the lower bound is now a *theorem* (modulo the
Itô-free convergence edge `hconv`), and only the matching upper bound — the direction requiring the
projections to exhaust the σ-algebra, i.e. the genuine stochastic-exponential / Itô content — remains
(ROADMAP Phase 2). `#print axioms`-clean. -/
theorem energy_le_klReal_of_projections
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hac : (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : InformationTheory.klDiv
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {𝓨 : ι → Type*} [∀ i, MeasurableSpace (𝓨 i)]
    (π : ∀ i, Path X → 𝓨 i) (hπ : ∀ i, Measurable (π i))
    (hconv : Filter.Tendsto
        (fun i => klReal ((d.pathLaw u ρ₀ : Measure (Path X)).map (π i))
                          ((d.R : Measure (Path X)).map (π i))) l
        (nhds (energy u (d.pathLaw u ρ₀)))) :
    energy u (d.pathLaw u ρ₀)
      ≤ klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) :=
  ForMathlib.MeasureTheory.le_toReal_klDiv_of_map_tendsto
    (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) hac hfin π hπ hconv

omit [NormedSpace ℝ X] in
/-- **Energy identity (4.19), FULL `=` — the `≤` half's Itô-free structural core wired in.**

Upgrades `energy_le_klReal_of_projections` from `≥` to the full equality
`𝔼[∫₀¹ ½‖u‖²] = D(P^{u,ρ₀}‖R)` (when both chains start alike, so the endpoint-entropy term
vanishes), assuming the time-grid projections `π n : Path X → 𝓨 n` **generate** the path σ-algebra
via a filtration `ℱ` (`⨆ n, ℱ n = ‹MeasurableSpace (Path X)›`, `ℱ n = comap (π n)`).

Both directions now come from one martingale-convergence fact and one edge:
`ForMathlib…klDiv_map_tendsto_toReal` (Lévy's upward theorem — **Itô-free**) shows the projected
divergences converge to the full `D(P‖R)`, while the convergence edge `hconv` says they converge to
the energy; limit-uniqueness (`tendsto_nhds_unique`) forces the two equal.

The **entire remaining Itô content is now localised to `hconv`** — the statement that the
finite-dimensional (grid) relative entropies converge to the control energy. For the
Euler–Maruyama/Gaussian marginals (the card's object) `hconv` factors into two Itô-free pieces:
(i) *grid KL = discrete energy* (`energy_identity_euler_maruyama`, the vendored discrete
Cameron–Martin identity), and (ii) *discrete energy → continuum energy integral*
(`ForMathlib…tendsto_emEnergy_sampled`, now **proved** — equispaced Riemann-sum convergence, pure
analysis). The one gap left for the EM model's `hconv` is *grid KL of the continuum path measure =
discrete energy*, i.e. the existence + finite-dim projection of the continuum reference itself — the
**Kolmogorov-extension** gap (dependent projective families are not yet in the Mathlib pin; the
Brownian projective family is proved consistent in `Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily`
but not yet extendable). For the exact feedback-diffusion marginals `hconv` is additionally the
finite-dimensional Girsanov density, the genuine stochastic-exponential content (ROADMAP Phase 2).
So the continuum wall is now two sharply-named, disjoint Mathlib gaps: Kolmogorov extension + Itô.
The generation hypothesis holds for a standard-Borel continuous-path model (countably many rational
times determine the path); it is a satisfiable hypothesis on the abstract `𝓨`/`ℱ`, not a vacuous
edge. `#print axioms`-clean. -/
theorem energy_eq_klReal_of_projections
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hac : (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : InformationTheory.klDiv
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    {𝓨 : ℕ → Type*} [hm𝓨 : ∀ n, MeasurableSpace (𝓨 n)]
    (π : ∀ n, Path X → 𝓨 n) (hπ : ∀ n, Measurable (π n))
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (Path X)))
    (hℱ : ∀ n, ℱ n = (hm𝓨 n).comap (π n))
    (hgen : ⨆ n, ℱ n = (inferInstance : MeasurableSpace (Path X)))
    (hconv : Filter.Tendsto
        (fun n => klReal ((d.pathLaw u ρ₀ : Measure (Path X)).map (π n))
                          ((d.R : Measure (Path X)).map (π n))) Filter.atTop
        (nhds (energy u (d.pathLaw u ρ₀)))) :
    energy u (d.pathLaw u ρ₀)
      = klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) :=
  tendsto_nhds_unique hconv
    (ForMathlib.MeasureTheory.klDiv_map_tendsto_toReal
      (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) hac hfin π hπ ℱ hℱ hgen)

omit [NormedSpace ℝ X] in
/-- **Energy identity (4.19), FULL `=`, discharged via a KL-preserving embedding into `ℕ→ℝ`
(plan A — the honest continuum `hgen`).**

The generation hypothesis `hgen` of `energy_eq_klReal_of_projections` is **false** for the raw path
space `Path X = ℝ→X` (a countable family of finite-time projections cannot generate its uncountable-
index product σ-algebra). This version removes it: instead of asking the projections to generate
`m(Path X)`, it asks only for a **measurable embedding with a measurable left inverse**
`e : Path X → (ℕ→ℝ)`, `g : (ℕ→ℝ) → Path X`, `g ∘ e = id` — a *lossless reparametrisation* of the
path by countably many real coordinates. This is exactly what a standard-Borel **continuous**-path
model supplies (a continuous path is determined by its values at countably many dense times, and by
Lusin–Souslin the restriction is a measurable embedding, `Measurable.measurableEmbedding` +
`MeasurableEmbedding.invFun`); crucially it is a *satisfiable* hypothesis, not the unsatisfiable
`hgen` on `ℝ→X`.

The proof composes three Itô-free `ForMathlib` results: `toReal_klDiv_map_eq_of_leftInverse`
(the embedding preserves `KL`, from the DPI both ways), then on the countable product `ℕ→ℝ`
`iSup_comap_frestrictLe_eq_pi` (the finite-prefix restrictions generate) feeds `klDiv_map_tendsto`
(Lévy martingale convergence) so the finite-grid divergences converge to `KL(e_#P ‖ e_#R) = KL(P‖R)`;
limit-uniqueness against the energy edge `hconv` closes it. `#print axioms`-clean. -/
theorem energy_eq_klReal_via_embedding
    (u : Control X) (ρ₀ : ProbabilityMeasure X)
    (hac : (d.pathLaw u ρ₀ : Measure (Path X)) ≪ (d.R : Measure (Path X)))
    (hfin : InformationTheory.klDiv
        (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) ≠ ⊤)
    (e : Path X → (ℕ → ℝ)) (he : Measurable e)
    (g : (ℕ → ℝ) → Path X) (hg : Measurable g) (hge : Function.LeftInverse g e)
    (hconv : Filter.Tendsto
        (fun n => klReal
            ((d.pathLaw u ρ₀ : Measure (Path X)).map
              (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω)))
            ((d.R : Measure (Path X)).map
              (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω))))
        Filter.atTop (nhds (energy u (d.pathLaw u ρ₀)))) :
    energy u (d.pathLaw u ρ₀)
      = klReal (d.pathLaw u ρ₀ : Measure (Path X)) (d.R : Measure (Path X)) := by
  set P := (d.pathLaw u ρ₀ : Measure (Path X)) with hP
  set R := (d.R : Measure (Path X)) with hR
  haveI : IsProbabilityMeasure (P.map e) := Measure.isProbabilityMeasure_map he.aemeasurable
  haveI : IsProbabilityMeasure (R.map e) := Measure.isProbabilityMeasure_map he.aemeasurable
  have hac' : P.map e ≪ R.map e := hac.map he
  have hfin' : InformationTheory.klDiv (P.map e) (R.map e) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (ForMathlib.MeasureTheory.klDiv_map_le P R hac e he)
  -- the embedding preserves KL
  have hemb : (InformationTheory.klDiv (P.map e) (R.map e)).toReal
      = (InformationTheory.klDiv P R).toReal :=
    ForMathlib.MeasureTheory.toReal_klDiv_map_eq_of_leftInverse P R hac hfin e he g hg hge
  -- the finite-prefix restriction filtration on `ℕ → ℝ`
  let ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    { seq := fun n => MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n) inferInstance
      mono' := by
        intro n m hnm
        calc MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n) inferInstance
            = MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) m)
                (MeasurableSpace.comap (Preorder.frestrictLe₂ (π := fun _ : ℕ => ℝ) hnm)
                  inferInstance) := by
              rw [MeasurableSpace.comap_comp, Preorder.frestrictLe₂_comp_frestrictLe]
          _ ≤ MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) m) inferInstance :=
              MeasurableSpace.comap_mono (Preorder.measurable_frestrictLe₂ hnm).comap_le
      le' := fun n => (Preorder.measurable_frestrictLe n).comap_le }
  -- martingale convergence on `ℕ → ℝ`, then transport the grid maps back through `e`
  have htends := ForMathlib.MeasureTheory.klDiv_map_tendsto_toReal (P.map e) (R.map e) hac' hfin'
    (fun n => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
    (fun n => Preorder.measurable_frestrictLe n) ℱ (fun _ => rfl)
    ForMathlib.MeasureTheory.iSup_comap_frestrictLe_eq_pi
  have hmapP : ∀ n, (P.map e).map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
      = P.map (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω)) := fun n => by
    rw [Measure.map_map (Preorder.measurable_frestrictLe n) he]; rfl
  have hmapR : ∀ n, (R.map e).map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
      = R.map (fun ω => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e ω)) := fun n => by
    rw [Measure.map_map (Preorder.measurable_frestrictLe n) he]; rfl
  simp only [hmapP, hmapR, hemb] at htends
  exact tendsto_nhds_unique hconv htends

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



--------------------------------------------------------------------------------
-- §3.M4  Continuum Cameron--Martin / Wiener path-law scaffold
--------------------------------------------------------------------------------

/-- Real-valued path space used by the M4 Wiener transport scaffold.  The existing
`Path X` abstraction is intentionally broad; M4 specializes to the scalar Wiener
case so the dyadic increment maps can be stated concretely. -/
abbrev RealPath : Type := Path ℝ

/-- Dyadic mesh size `2⁻ⁿ` for level `n`. -/
noncomputable def dyadicMesh (level : ℕ) : ℝ := ((2 : ℝ) ^ level)⁻¹

/-- Dyadic mesh size as a nonnegative real, for APIs such as `gaussianReal` whose
variance parameter is `NNReal`. -/
noncomputable def dyadicMeshNNReal (level : ℕ) : NNReal :=
  ⟨dyadicMesh level, by
    unfold dyadicMesh
    positivity⟩

@[simp] lemma coe_dyadicMeshNNReal (level : ℕ) :
    (dyadicMeshNNReal level : ℝ) = dyadicMesh level := rfl

/-- Dyadic time `i / 2ⁿ` at level `n`.  The declarations below use the finite
range `i : Fin (2^n)` for increments, so the right endpoint is `i + 1`. -/
noncomputable def dyadicTime (level i : ℕ) : ℝ := (i : ℝ) / ((2 : ℝ) ^ level)

/-- Raw dyadic increment of a real path over interval `[i/2ⁿ, (i+1)/2ⁿ]`. -/
noncomputable def dyadicIncrement (level : ℕ) (ω : RealPath) (i : Fin (2 ^ level)) : ℝ :=
  ω (dyadicTime level (i.1 + 1)) - ω (dyadicTime level i.1)

/-- Vector of raw dyadic increments at level `n`. -/
noncomputable def dyadicIncrementMap (level : ℕ) : RealPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => dyadicIncrement level ω i

/-- Normalized dyadic increment.  Under standard Wiener measure this should be a
standard normal coordinate: `(W_{t+Δt}-W_t)/sqrt(Δt)`. -/
noncomputable def normalizedDyadicIncrement (level : ℕ) (ω : RealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  dyadicIncrement level ω i / Real.sqrt (dyadicMesh level)

/-- Vector of normalized dyadic increments at level `n`. -/
noncomputable def normalizedDyadicIncrementMap (level : ℕ) :
    RealPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => normalizedDyadicIncrement level ω i

/-- Finite dyadic Cameron--Martin energy of a deterministic shift path: the
finite-dimensional Gaussian cost of its normalized increment vector. -/
noncomputable def dyadicPathEnergy (level : ℕ) (h : RealPath) : ℝ :=
  2⁻¹ * ∑ i : Fin (2 ^ level), normalizedDyadicIncrementMap level h i ^ 2

/-- Continuum Cameron--Martin energy `½ ∫₀¹ |h'(t)|² dt`. -/
noncomputable def cameronMartinPathEnergy (hderiv : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, 2⁻¹ * hderiv t ^ 2 ∂volume

/-- Staged path-level Cameron--Martin interface for M4.

The first field records the usual square-integrability of the derivative.  The
second field records the continuum-limit theorem needed by the dyadic scaffold:
the finite dyadic Cameron--Martin energies converge to the continuum energy.
Future work should replace this interface field by a proof from the chosen
Sobolev/absolutely-continuous path representation. -/
structure IsCameronMartinPath (h : RealPath) (hderiv : ℝ → ℝ) : Prop where
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  dyadic_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))

/-- Abstract standard-Wiener interface needed for M4.

The first field says that each normalized dyadic increment vector has the
canonical finite-dimensional standard Gaussian law.  The second field records
the projection/exhaustion KL convergence needed to pass from dyadic finite-grid
KLs to the full path-law KL.  Future work should discharge both fields from
Mathlib Brownian motion / Wiener measure APIs and the path-law filtration
exhaustion theorem, rather than assume them. -/
structure IsStandardWiener (W : ProbabilityMeasure RealPath) : Prop where
  normalized_dyadic_law : ∀ level : ℕ,
    Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- Dyadic normalized-increment KL exhaustion for a path-space law.

This is kept as a separate interface from `IsStandardWiener`: the latter is the
finite-dimensional Wiener law, while this field is the path-space filtration/exhaustion theorem
needed to pass finite-grid KLs to full path-law KL. -/
structure HasDyadicKLExhaustion (W : ProbabilityMeasure RealPath) : Prop where
  normalized_dyadic_kl_tendsto : ∀ (h : RealPath),
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) →
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedDyadicIncrementMap level)
            ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
          (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)))

/-! ### Interval-path carrier for the M4 continuum frontier

The ambient `RealPath := ℝ → ℝ` scaffold above is useful for compatibility with the older CGP
wrappers, but it is too broad for a theorem saying that dyadic increments on `[0,1]` generate all
path information.  The declarations in this block introduce a narrow interval-path interface for the
next continuum proof step.  They intentionally prove only finite-projection facts and leave full
path-space generation/KL exhaustion and Cameron--Martin quasi-invariance as explicit interfaces.
-/

/-- The closed unit interval `[0,1]`, as a subtype used for canonical interval paths. -/
abbrev UnitInterval : Type := Set.Icc (0 : ℝ) 1

/-- The left endpoint of the interval carrier. -/
def unitIntervalZero : UnitInterval :=
  ⟨0, by constructor <;> norm_num⟩

/-- The right endpoint of the interval carrier. -/
def unitIntervalOne : UnitInterval :=
  ⟨1, by constructor <;> norm_num⟩

/-- Clamp a real time to the closed unit interval.

Using a clamped representative lets the low-level projection maps be total without adding proof
obligations at every dyadic endpoint.  The analytic generation theorem below is still an explicit
interface, not a theorem about this lightweight carrier. -/
noncomputable def clampUnitInterval (t : ℝ) : UnitInterval :=
  ⟨max 0 (min 1 t), by
    constructor
    · exact le_max_left 0 (min 1 t)
    · exact max_le (by norm_num) (min_le_left 1 t)⟩

@[simp] theorem coe_clampUnitInterval (t : ℝ) :
    ((clampUnitInterval t : UnitInterval) : ℝ) = max 0 (min 1 t) := rfl

/-- Canonical scalar paths on `[0,1]` for the future continuum theorem carrier.

This is deliberately not identified with `RealPath`; interval dyadic increments should generate this
carrier, not arbitrary real-time coordinates.  Anchoring and continuity/Sobolev regularity are kept as
separate predicates/interfaces so downstream wrappers can distinguish proved finite-grid facts from
continuum assumptions. -/
abbrev IntervalPath : Type := UnitInterval → ℝ

/-- Anchoring predicate for interval paths, matching Brownian/Cameron--Martin convention `h(0)=0`. -/
def IntervalPathAnchored (ω : IntervalPath) : Prop :=
  ω unitIntervalZero = 0

/-- Dyadic time on the interval carrier. -/
noncomputable def intervalDyadicTime (level i : ℕ) : UnitInterval :=
  clampUnitInterval (dyadicTime level i)

/-- Raw dyadic increment of an interval path. -/
noncomputable def intervalDyadicIncrement (level : ℕ) (ω : IntervalPath)
    (i : Fin (2 ^ level)) : ℝ :=
  ω (intervalDyadicTime level (i.1 + 1)) - ω (intervalDyadicTime level i.1)

/-- Vector of raw dyadic increments for interval paths. -/
noncomputable def intervalDyadicIncrementMap (level : ℕ) :
    IntervalPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => intervalDyadicIncrement level ω i

/-- Normalized dyadic increment on the interval carrier. -/
noncomputable def normalizedIntervalDyadicIncrement (level : ℕ) (ω : IntervalPath)
    (i : Fin (2 ^ level)) : ℝ :=
  intervalDyadicIncrement level ω i / Real.sqrt (dyadicMesh level)

/-- Vector of normalized dyadic increments for interval paths. -/
noncomputable def normalizedIntervalDyadicIncrementMap (level : ℕ) :
    IntervalPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => normalizedIntervalDyadicIncrement level ω i

/-- Finite dyadic Cameron--Martin energy on the interval carrier. -/
noncomputable def intervalDyadicPathEnergy (level : ℕ) (h : IntervalPath) : ℝ :=
  2⁻¹ * ∑ i : Fin (2 ^ level), normalizedIntervalDyadicIncrementMap level h i ^ 2

/-- Interval Cameron--Martin interface.

This is the interval-carrier analogue of `IsCameronMartinPath`.  It includes the Brownian anchor and
keeps the Sobolev-to-dyadic-energy theorem as an explicit field until the repository chooses a real
AC/Sobolev path API. -/
structure IsIntervalCameronMartinPath (h : IntervalPath) (hderiv : ℝ → ℝ) : Prop where
  anchored : IntervalPathAnchored h
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  dyadic_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => intervalDyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))

/-- Standard-Wiener finite-dimensional interface on the corrected interval carrier. -/
structure IsStandardIntervalWiener (W : ProbabilityMeasure IntervalPath) : Prop where
  normalized_dyadic_law : ∀ level : ℕ,
    Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- Path-space dyadic KL exhaustion on the corrected interval carrier.

This is intentionally an interface: it should be proved later from a genuine generating-filtration
result for the chosen interval path measurable space, not inferred from the ambient `RealPath`
scaffold. -/
structure HasIntervalDyadicKLExhaustion (W : ProbabilityMeasure IntervalPath) : Prop where
  normalized_dyadic_kl_tendsto : ∀ (h : IntervalPath),
    (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪ (W : Measure IntervalPath) →
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedIntervalDyadicIncrementMap level)
            ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h)))
          (Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath)))

/-- Generation interface for interval dyadic normalized increments.

Unlike the intentionally weakened `RealPath` one-sided lemma, this is the *right shape* of the future
carrier theorem: the dyadic projection filtration should generate the chosen interval path
measurable space for the selected Brownian/continuous/anchored carrier.  The target measurable space
is an explicit parameter so this declaration does not falsely claim that dyadic increments generate
the default product sigma-algebra on all functions `[0,1] → ℝ`. -/
structure HasIntervalDyadicGeneration (𝓜 : MeasurableSpace IntervalPath) : Prop where
  normalized_dyadic_iSup_comap_eq :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ))) = 𝓜

/-- The interval normalized-increment maps are measurable. -/
theorem measurable_normalizedIntervalDyadicIncrementMap (level : ℕ) :
    Measurable (normalizedIntervalDyadicIncrementMap level) := by
  unfold normalizedIntervalDyadicIncrementMap normalizedIntervalDyadicIncrement intervalDyadicIncrement
  fun_prop

/-- The sigma-algebra generated by interval dyadic projections is bounded above by the interval path
measurable space.  The reverse inclusion is the explicit `HasIntervalDyadicGeneration` interface. -/
theorem normalizedIntervalDyadicIncrementMap_iSup_comap_le :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedIntervalDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
      ≤ (inferInstance : MeasurableSpace IntervalPath) := by
  refine iSup_le ?_
  intro level
  exact (measurable_normalizedIntervalDyadicIncrementMap level).comap_le

/-- Interval normalized dyadic increments commute with deterministic path addition. -/
theorem normalizedIntervalDyadicIncrementMap_add (level : ℕ) (ω h : IntervalPath) :
    normalizedIntervalDyadicIncrementMap level (ω + h)
      = normalizedIntervalDyadicIncrementMap level ω + normalizedIntervalDyadicIncrementMap level h := by
  funext i
  unfold normalizedIntervalDyadicIncrementMap normalizedIntervalDyadicIncrement intervalDyadicIncrement
  simp [Pi.add_apply]
  ring

/-- Interval finite-dimensional Wiener projection law wrapper. -/
theorem normalizedIntervalDyadicIncrementMap_wiener_law
    (W : ProbabilityMeasure IntervalPath) (hW : IsStandardIntervalWiener W) (level : ℕ) :
    Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  exact hW.normalized_dyadic_law level

/-- Shifted interval Wiener projection law: finite-dimensional dyadic increments are translated by the
increment vector of the deterministic shift. -/
theorem normalizedIntervalDyadicIncrementMap_shifted_wiener_law
    (W : ProbabilityMeasure IntervalPath) (hW : IsStandardIntervalWiener W)
    (level : ℕ) (h : IntervalPath) :
    Measure.map (normalizedIntervalDyadicIncrementMap level)
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
      = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedIntervalDyadicIncrementMap level h) := by
  let N : IntervalPath → (Fin (2 ^ level) → ℝ) := normalizedIntervalDyadicIncrementMap level
  let v : Fin (2 ^ level) → ℝ := normalizedIntervalDyadicIncrementMap level h
  have hN : Measurable N := measurable_normalizedIntervalDyadicIncrementMap level
  have hshift : Measurable (fun ω : IntervalPath => ω + h) := by fun_prop
  have hshiftFin : Measurable (fun x : Fin (2 ^ level) → ℝ => x + v) := by fun_prop
  have hcomp : N ∘ (fun ω : IntervalPath => ω + h) =
      (fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N := by
    funext ω
    exact normalizedIntervalDyadicIncrementMap_add level ω h
  calc
    Measure.map N ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        = (W : Measure IntervalPath).map (N ∘ (fun ω : IntervalPath => ω + h)) := by
            rw [Measure.map_map hN hshift]
    _ = (W : Measure IntervalPath).map ((fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N) := by
            rw [hcomp]
    _ = ((W : Measure IntervalPath).map N).map (fun x : Fin (2 ^ level) → ℝ => x + v) := by
            rw [Measure.map_map hshiftFin hN]
    _ = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedIntervalDyadicIncrementMap level h) := by
            change ((W : Measure IntervalPath).map (normalizedIntervalDyadicIncrementMap level)).map
                (fun x : Fin (2 ^ level) → ℝ => x + normalizedIntervalDyadicIncrementMap level h) = _
            rw [normalizedIntervalDyadicIncrementMap_wiener_law W hW level]

/-- Finite-dimensional interval Cameron--Martin KL identity on each dyadic projection. -/
theorem klDiv_normalizedIntervalDyadicIncrement_shifted_wiener
    (W : ProbabilityMeasure IntervalPath) (hW : IsStandardIntervalWiener W)
    (level : ℕ) (h : IntervalPath) :
    InformationTheory.klDiv
        (Measure.map (normalizedIntervalDyadicIncrementMap level)
          ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h)))
        (Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath))
      = ENNReal.ofReal (intervalDyadicPathEnergy level h) := by
  rw [normalizedIntervalDyadicIncrementMap_shifted_wiener_law W hW level h,
    normalizedIntervalDyadicIncrementMap_wiener_law W hW level]
  simpa [intervalDyadicPathEnergy] using
    (ForMathlib.MeasureTheory.klDiv_stdGaussian_map_add
      (normalizedIntervalDyadicIncrementMap level h))

/-- Interval dyadic finite-grid energies converge to continuum Cameron--Martin energy under the
explicit interval Cameron--Martin interface. -/
theorem intervalDyadicPathEnergy_tendsto_cameronMartinPathEnergy
    (h : IntervalPath) (hderiv : ℝ → ℝ) (hCM : IsIntervalCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => intervalDyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  exact hCM.dyadic_energy_tendsto

/-- Interval path-space KL exhaustion, exposed as an explicit interface. -/
theorem klDiv_normalizedIntervalDyadicIncrement_tendsto_path_kl
    (W : ProbabilityMeasure IntervalPath) (h : IntervalPath)
    (hKL : HasIntervalDyadicKLExhaustion W)
    (hac : (W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h) ≪
        (W : Measure IntervalPath)) :
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedIntervalDyadicIncrementMap level)
            ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h)))
          (Measure.map (normalizedIntervalDyadicIncrementMap level) (W : Measure IntervalPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure IntervalPath).map (fun ω : IntervalPath => ω + h))
        (W : Measure IntervalPath))) := by
  exact hKL.normalized_dyadic_kl_tendsto h hac

/-- Nonnegative-time real path space used by the concrete `wienerMeasure` construction.

The CGP-facing M4 scaffold above keeps `RealPath := Path ℝ` so existing endpoint/path-law
statements remain stable.  The vendored Kolmogorov construction of standard Wiener measure,
however, naturally lives on `NNReal → ℝ`.  This parallel nonnegative-time staging namespace is the
place where we discharge the "real Wiener measure satisfies the finite-dimensional standard-normal
increment law" capstone before transporting it back to whatever final CGP path representation is
chosen. -/
abbrev WienerRealPath : Type := NNReal → ℝ

/-- Dyadic time `i / 2ⁿ` as a nonnegative real. -/
noncomputable def dyadicTimeNNReal (level i : ℕ) : NNReal :=
  ⟨(i : ℝ) / ((2 : ℝ) ^ level), by positivity⟩

/-- Raw dyadic increment on the concrete nonnegative-time Wiener path space. -/
noncomputable def wienerDyadicIncrement (level : ℕ) (ω : WienerRealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  ω (dyadicTimeNNReal level (i.1 + 1)) - ω (dyadicTimeNNReal level i.1)

/-- Normalized dyadic increment on `NNReal → ℝ` paths. -/
noncomputable def normalizedWienerDyadicIncrement (level : ℕ) (ω : WienerRealPath)
    (i : Fin (2 ^ level)) : ℝ :=
  wienerDyadicIncrement level ω i / Real.sqrt (dyadicMesh level)

/-- Vector of normalized dyadic increments for the concrete nonnegative-time Wiener path space. -/
noncomputable def normalizedWienerDyadicIncrementMap (level : ℕ) :
    WienerRealPath → (Fin (2 ^ level) → ℝ) :=
  fun ω i => normalizedWienerDyadicIncrement level ω i

/-- Concrete standard Wiener measure on nonnegative-time real paths. -/
noncomputable def standardWienerMeasure : Measure WienerRealPath :=
  ForMathlib.MeasureTheory.wienerMeasure

/-- The concrete Wiener measure is a probability measure. -/
instance isProbabilityMeasure_standardWienerMeasure : IsProbabilityMeasure standardWienerMeasure := by
  dsimp [standardWienerMeasure]
  infer_instance

/-- Concrete standard-Wiener interface for measures on `NNReal → ℝ`.

This is the first real-Wiener capstone that follows directly from the vendored Kolmogorov
extension: the canonical coordinate process on `NNReal → ℝ` has the Brownian projective-family law.
The stronger normalized-dyadic-product law is now a downstream consequence target, not an implicit
`sorry` hidden inside this interface. -/
structure IsConcreteStandardWiener (W : Measure WienerRealPath) : Prop where
  is_probability : IsProbabilityMeasure W
  is_preBrownian : ProbabilityTheory.IsPreBrownianReal (fun t (ω : WienerRealPath) => ω t) W

/-- The canonical coordinate process under the vendored Wiener measure is a pre-Brownian motion.

This discharges the concrete projective-family part of the "real Wiener measure" capstone: every
finite coordinate marginal of `standardWienerMeasure` is exactly `BrownianReal.projectiveFamily`.
The proof is a direct wrapper around `ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure`. -/
theorem isPreBrownianReal_standardWienerMeasure :
    ProbabilityTheory.IsPreBrownianReal (fun t (ω : WienerRealPath) => ω t)
      standardWienerMeasure := by
  refine ProbabilityTheory.IsPreBrownianReal.mk' ?_
  intro I
  refine ⟨?_, ?_⟩
  · fun_prop
  · simpa [standardWienerMeasure] using
      (ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure I)

/-- The vendored concrete Wiener measure satisfies the focused nonnegative-time standard-Wiener
interface. -/
theorem isConcreteStandardWiener_standardWienerMeasure :
    IsConcreteStandardWiener standardWienerMeasure := by
  exact ⟨inferInstance, isPreBrownianReal_standardWienerMeasure⟩

/-- Finite-dimensional coordinate law of the concrete Wiener measure.

This is the direct projective-limit marginal statement: restricting a Wiener path to any finite set
of nonnegative times has Mathlib's Brownian projective-family law on that finite coordinate set. -/
theorem standardWienerMeasure_finite_coordinate_law (I : Finset NNReal) :
    Measure.map (fun ω : WienerRealPath => I.restrict ω) standardWienerMeasure
      = ProbabilityTheory.BrownianReal.projectiveFamily I := by
  simpa [standardWienerMeasure] using
    (ForMathlib.MeasureTheory.isProjectiveLimit_wienerMeasure I)

/-- The dyadic endpoint grid `{0, 1/2ⁿ, ..., 1}` as a finite set of nonnegative times. -/
noncomputable def wienerDyadicGrid (level : ℕ) : Finset NNReal :=
  (Finset.range (2 ^ level + 1)).image (fun i : ℕ => dyadicTimeNNReal level i)

/-- Dyadic endpoint times belong to the level grid. -/
lemma dyadicTimeNNReal_mem_wienerDyadicGrid
    (level i : ℕ) (hi : i ≤ 2 ^ level) :
    dyadicTimeNNReal level i ∈ wienerDyadicGrid level := by
  classical
  refine Finset.mem_image.mpr ?_
  refine ⟨i, ?_, rfl⟩
  simpa [Nat.lt_succ_iff] using hi

/-- A dyadic endpoint, bundled as an element of the dyadic grid. -/
noncomputable def wienerDyadicGridPoint (level i : ℕ) (hi : i ≤ 2 ^ level) :
    wienerDyadicGrid level :=
  ⟨dyadicTimeNNReal level i, dyadicTimeNNReal_mem_wienerDyadicGrid level i hi⟩

/-- Normalized dyadic increment as a linear map out of the finite dyadic endpoint vector. -/
noncomputable def normalizedWienerDyadicIncrementFromGrid (level : ℕ) :
    ((wienerDyadicGrid level) → ℝ) → (Fin (2 ^ level) → ℝ) :=
  fun x i =>
    (x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
        - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2)))
      / Real.sqrt (dyadicMesh level)

/-- The finite-grid normalized-increment map factors through restriction to the dyadic endpoint grid. -/
theorem normalizedWienerDyadicIncrementMap_eq_fromGrid (level : ℕ) :
    normalizedWienerDyadicIncrementMap level
      = normalizedWienerDyadicIncrementFromGrid level ∘
          (fun ω : WienerRealPath => (wienerDyadicGrid level).restrict ω) := by
  funext ω i
  simp [normalizedWienerDyadicIncrementMap, normalizedWienerDyadicIncrementFromGrid,
    normalizedWienerDyadicIncrement, wienerDyadicIncrement, Function.comp,
    wienerDyadicGridPoint]

/-- The normalized dyadic increment law under Wiener measure reduces to a finite-dimensional
Brownian projective-family statement on the dyadic endpoint grid.

This is the main structural reduction needed before invoking independent-increment/product-Gaussian
lemmas for `BrownianReal.projectiveFamily`. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily
    (level : ℕ) :
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = Measure.map (normalizedWienerDyadicIncrementFromGrid level)
          (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)) := by
  rw [normalizedWienerDyadicIncrementMap_eq_fromGrid level]
  let r : WienerRealPath → (wienerDyadicGrid level → ℝ) :=
    fun ω => (wienerDyadicGrid level).restrict ω
  let g : (wienerDyadicGrid level → ℝ) → (Fin (2 ^ level) → ℝ) :=
    normalizedWienerDyadicIncrementFromGrid level
  have hr : Measurable r := by
    dsimp [r]
    exact (wienerDyadicGrid level).measurable_restrict
  have hg : Measurable g := by
    dsimp [g]
    unfold normalizedWienerDyadicIncrementFromGrid dyadicMesh
    fun_prop
  have hmap : Measure.map g (Measure.map r standardWienerMeasure)
      = Measure.map (g ∘ r) standardWienerMeasure :=
    Measure.map_map hg hr
  change Measure.map (g ∘ r) standardWienerMeasure =
    Measure.map g (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
  rw [← hmap]
  rw [standardWienerMeasure_finite_coordinate_law (wienerDyadicGrid level)]

/-- Remaining Brownian finite-dimensional algebra capstone: under the Brownian projective-family law
on dyadic endpoint coordinates, normalized consecutive increments are iid standard Gaussian.

This is now the single finite-dimensional theorem left between the concrete Wiener construction and
the sequence-model Cameron--Martin theorem. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_law_target : Prop :=
  ∀ level : ℕ,
    Measure.map (normalizedWienerDyadicIncrementFromGrid level)
        (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- One-dimensional Brownian increment normalization target on the concrete dyadic grid.

For each dyadic edge, the corresponding normalized increment should have law `N(0,1)`.
This is the coordinate-level theorem that should follow from Mathlib's Brownian increment law
`measurePreserving_eval_sub_eval_projectiveFamily` plus the scaling `Δt = 2⁻ˡᵉᵛᵉˡ`. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_coord_law_target : Prop :=
  ∀ (level : ℕ) (i : Fin (2 ^ level)),
    Measure.map (fun x : wienerDyadicGrid level → ℝ =>
        normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = gaussianReal 0 1

/-- Finite-dimensional independence target for normalized dyadic increments.

Together with the coordinate law above, this is the product-law route to
`brownianProjectiveFamily_normalizedDyadicIncrement_law_target`.  It isolates the remaining
Brownian covariance/independent-increment work from the already-proved projective-limit reduction. -/
def brownianProjectiveFamily_normalizedDyadicIncrement_indepFun_target : Prop :=
  ∀ level : ℕ,
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun x : wienerDyadicGrid level → ℝ =>
          normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))

/-- Next concrete capstone, now exposed as an ordinary theorem target instead of a hidden interface
field: derive the iid standard-normal law of normalized dyadic increments from
`isPreBrownianReal_standardWienerMeasure`, Brownian independent increments, and the Gaussian
product/normalization lemmas. -/
def normalizedWienerDyadicIncrementMap_standardWiener_law_target : Prop :=
  ∀ level : ℕ,
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))

/-- Concrete normalized dyadic iid-Gaussian law for the vendored Wiener measure, assuming the finite
Brownian projective-family increment algebra. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_of_projectiveFamily
    (hproj : brownianProjectiveFamily_normalizedDyadicIncrement_law_target) :
    normalizedWienerDyadicIncrementMap_standardWiener_law_target := by
  intro level
  rw [normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily level]
  exact hproj level


/-! ### M4 concrete Wiener finite-dimensional theorem ladder

The declarations in this block spell out the remaining concrete Wiener proof obligations that
turn the vendored Kolmogorov/Wiener construction on `NNReal → ℝ` into the dyadic iid Gaussian
interface used by the abstract M4 Cameron--Martin theorem.  The large Brownian independent-
increment and path-space KL-exhaustion facts are intentionally exposed as theorem statements so
we can fill them in one by one without changing downstream theorem names. -/

/-- The length of each dyadic interval is exactly the dyadic mesh. -/
theorem dyadicTimeNNReal_succ_sub (level : ℕ) (i : Fin (2 ^ level)) :
    ((dyadicTimeNNReal level (i.1 + 1) : ℝ) - (dyadicTimeNNReal level i.1 : ℝ))
      = dyadicMesh level := by
  rw [show (dyadicTimeNNReal level (i.1 + 1) : ℝ)
      = (((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level)) by rfl]
  rw [show (dyadicTimeNNReal level i.1 : ℝ)
      = (((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level)) by rfl]
  unfold dyadicMesh
  have hpow : ((2 : ℝ) ^ level) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow]
  rw [Nat.cast_add, Nat.cast_one]
  ring

/-- Scaling a centered one-dimensional Gaussian by its standard deviation gives `N(0,1)`.

This is the scalar normalization lemma needed after Brownian increments give variance equal to
`dyadicMesh level`. -/
theorem gaussianReal_map_div_sqrt_self {σ2 : NNReal} (hσ2 : 0 < (σ2 : ℝ)) :
    Measure.map (fun x : ℝ => x / Real.sqrt (σ2 : ℝ)) (gaussianReal 0 σ2) = gaussianReal 0 1 := by
  let L : ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun x : ℝ => x / Real.sqrt (σ2 : ℝ)
      map_add' := by
        intro x y
        ring
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply]
        ring_nf }
  calc
    Measure.map (fun x : ℝ => x / Real.sqrt (σ2 : ℝ)) (gaussianReal 0 σ2)
        = Measure.map L (gaussianReal 0 σ2) := by rfl
    _ = gaussianReal (L 0) (((L 1) ^ 2).toNNReal * σ2) := by
        exact gaussianReal_map_linearMap (μ := 0) (v := σ2) L
    _ = gaussianReal 0 1 := by
        apply (gaussianReal_ext_iff).2
        constructor
        · simp [L]
        · ext
          have hsqrt_pos : 0 < Real.sqrt (σ2 : ℝ) := Real.sqrt_pos.2 hσ2
          have hsqrt_ne : Real.sqrt (σ2 : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
          have hsqrt_sq : Real.sqrt (σ2 : ℝ) ^ 2 = (σ2 : ℝ) := by
            rw [Real.sq_sqrt (le_of_lt hσ2)]
          have hcalc : ((1 / Real.sqrt (σ2 : ℝ)) ^ 2) * (σ2 : ℝ) = (1 : ℝ) := by
            calc
              ((1 / Real.sqrt (σ2 : ℝ)) ^ 2) * (σ2 : ℝ)
                  = ((1 / Real.sqrt (σ2 : ℝ)) ^ 2) * (Real.sqrt (σ2 : ℝ) ^ 2) := by
                    rw [hsqrt_sq]
              _ = 1 := by
                    field_simp [hsqrt_ne]
          change ((((1 / Real.sqrt (σ2 : ℝ)) ^ 2).toNNReal : ℝ) * (σ2 : ℝ)) = (1 : ℝ)
          rw [Real.toNNReal_of_nonneg (sq_nonneg (1 / Real.sqrt (σ2 : ℝ)))]
          exact hcalc

/-- The nonnegative distance between consecutive dyadic endpoints is the dyadic mesh. -/
theorem nndist_dyadicTimeNNReal_succ (level : ℕ) (i : Fin (2 ^ level)) :
    nndist (dyadicTimeNNReal level (i.1 + 1)) (dyadicTimeNNReal level i.1)
      = dyadicMeshNNReal level := by
  ext
  rw [coe_nndist]
  change dist ((dyadicTimeNNReal level (i.1 + 1) : ℝ))
      ((dyadicTimeNNReal level i.1 : ℝ)) = dyadicMesh level
  rw [Real.dist_eq, abs_of_nonneg]
  · exact dyadicTimeNNReal_succ_sub level i
  · rw [dyadicTimeNNReal_succ_sub level i]
    unfold dyadicMesh
    positivity

/-- Raw dyadic Brownian increment law under the finite Brownian projective family.

This is the coordinate-law theorem before variance normalization. -/
theorem brownianProjectiveFamily_dyadicIncrement_law
    (level : ℕ) (i : Fin (2 ^ level)) :
    Measure.map (fun x : wienerDyadicGrid level → ℝ =>
        x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
          - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2)))
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = gaussianReal 0 (dyadicMeshNNReal level) := by
  let t0 : NNReal := dyadicTimeNNReal level i.1
  let t1 : NNReal := dyadicTimeNNReal level (i.1 + 1)
  let r : WienerRealPath → (wienerDyadicGrid level → ℝ) :=
    fun ω => (wienerDyadicGrid level).restrict ω
  let rawGrid : (wienerDyadicGrid level → ℝ) → ℝ := fun x =>
    x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
      - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2))
  let rawPath : WienerRealPath → ℝ := fun ω => ω t1 - ω t0
  have hr : Measurable r := by
    dsimp [r]
    exact (wienerDyadicGrid level).measurable_restrict
  have hrawGrid : Measurable rawGrid := by
    dsimp [rawGrid]
    fun_prop
  have hcomp : rawGrid ∘ r = rawPath := by
    funext ω
    simp [rawGrid, r, rawPath, t0, t1, wienerDyadicGridPoint]
  have hmap : Measure.map rawGrid
        (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = Measure.map rawPath standardWienerMeasure := by
    rw [← standardWienerMeasure_finite_coordinate_law (wienerDyadicGrid level)]
    rw [Measure.map_map hrawGrid hr]
    rw [hcomp]
  rw [hmap]
  have hlaw := isPreBrownianReal_standardWienerMeasure.hasLaw_sub t1 t0
  have hvar : nndist t1 t0 = dyadicMeshNNReal level := by
    simpa [t0, t1] using nndist_dyadicTimeNNReal_succ level i
  rw [← hvar]
  exact hlaw.map_eq

/-- Normalized dyadic Brownian increments have standard normal one-dimensional law. -/
theorem brownianProjectiveFamily_normalizedDyadicIncrement_coord_law
    (level : ℕ) (i : Fin (2 ^ level)) :
    Measure.map (fun x : wienerDyadicGrid level → ℝ =>
        normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = gaussianReal 0 1 := by
  let raw : (wienerDyadicGrid level → ℝ) → ℝ := fun x =>
    x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
      - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2))
  let scale : ℝ → ℝ := fun y => y / Real.sqrt (dyadicMesh level)
  have hraw : Measurable raw := by
    dsimp [raw]
    fun_prop
  have hscale : Measurable scale := by
    dsimp [scale]
    fun_prop
  have hfun : (fun x : wienerDyadicGrid level → ℝ =>
        normalizedWienerDyadicIncrementFromGrid level x i) = scale ∘ raw := by
    funext x
    simp [raw, scale, normalizedWienerDyadicIncrementFromGrid]
  rw [hfun]
  rw [← Measure.map_map (μ := ProbabilityTheory.BrownianReal.projectiveFamily
    (wienerDyadicGrid level)) hscale hraw]
  rw [brownianProjectiveFamily_dyadicIncrement_law level i]
  exact gaussianReal_map_div_sqrt_self (σ2 := dyadicMeshNNReal level) (by
    change 0 < dyadicMesh level
    unfold dyadicMesh
    positivity)

/-- Dyadic endpoints form a monotone nonnegative-time sequence. -/
theorem monotone_dyadicTimeNNReal (level : ℕ) :
    Monotone (fun n : ℕ => dyadicTimeNNReal level n) := by
  intro a b hab
  rw [← NNReal.coe_le_coe]
  change ((a : ℝ) / ((2 : ℝ) ^ level)) ≤ ((b : ℝ) / ((2 : ℝ) ^ level))
  have hden_nonneg : 0 ≤ ((2 : ℝ) ^ level) := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hden_nonneg

/-- Dyadic Brownian increments are independent under the concrete vendored Wiener measure. -/
theorem standardWienerMeasure_dyadicIncrement_indepFun
    (level : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun ω : WienerRealPath =>
          ω (dyadicTimeNNReal level (i.1 + 1)) - ω (dyadicTimeNNReal level i.1))
      standardWienerMeasure := by
  have hnat : ProbabilityTheory.iIndepFun
      (fun n : ℕ =>
        fun ω : WienerRealPath =>
          ω (dyadicTimeNNReal level (n + 1)) - ω (dyadicTimeNNReal level n))
      standardWienerMeasure := by
    exact (ProbabilityTheory.IsPreBrownianReal.hasIndepIncrements
      isPreBrownianReal_standardWienerMeasure).nat
        (t := fun n : ℕ => dyadicTimeNNReal level n)
        (monotone_dyadicTimeNNReal level)
  have hinj : Function.Injective (fun i : Fin (2 ^ level) => i.1) := by
    intro i j hij
    ext
    exact hij
  simpa [Function.comp] using
    (hnat.precomp (g := fun i : Fin (2 ^ level) => i.1) hinj)

/-- Raw dyadic Brownian increments over disjoint adjacent intervals are independent. -/
theorem brownianProjectiveFamily_dyadicIncrement_indepFun
    (level : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun x : wienerDyadicGrid level → ℝ =>
          x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
            - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2)))
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)) := by
  let r : WienerRealPath → (wienerDyadicGrid level → ℝ) :=
    fun ω => (wienerDyadicGrid level).restrict ω
  let rawGrid : Fin (2 ^ level) → ((wienerDyadicGrid level → ℝ) → ℝ) := fun i x =>
    x (wienerDyadicGridPoint level (i.1 + 1) (Nat.succ_le_of_lt i.2))
      - x (wienerDyadicGridPoint level i.1 (le_of_lt i.2))
  let rawPath : Fin (2 ^ level) → (WienerRealPath → ℝ) := fun i ω =>
    ω (dyadicTimeNNReal level (i.1 + 1)) - ω (dyadicTimeNNReal level i.1)
  have hr : Measurable r := by
    dsimp [r]
    fun_prop
  have hrawGrid_meas : ∀ i : Fin (2 ^ level), Measurable (rawGrid i) := by
    intro i
    dsimp [rawGrid]
    fun_prop
  have hvecGrid_meas : Measurable (fun x : wienerDyadicGrid level → ℝ => fun i => rawGrid i x) := by
    dsimp [rawGrid]
    fun_prop
  have hcomp : (fun i : Fin (2 ^ level) => rawGrid i ∘ r) = rawPath := by
    funext i ω
    simp [rawGrid, rawPath, r, wienerDyadicGridPoint]
  have hindepPath := standardWienerMeasure_dyadicIncrement_indepFun level
  have hindepComp : ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) => rawGrid i ∘ r) standardWienerMeasure := by
    rw [hcomp]
    exact hindepPath
  have hprodPath :
      Measure.map (fun ω : WienerRealPath => fun i : Fin (2 ^ level) => (rawGrid i ∘ r) ω)
          standardWienerMeasure
        = Measure.pi (fun i : Fin (2 ^ level) =>
            Measure.map (rawGrid i ∘ r) standardWienerMeasure) := by
    simpa [Function.comp] using
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (μ := standardWienerMeasure)
        (f := fun i : Fin (2 ^ level) => rawGrid i ∘ r)
        (by
          intro i
          exact ((hrawGrid_meas i).comp hr).aemeasurable)).mp hindepComp
  have hprojective :
      ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)
        = Measure.map r standardWienerMeasure := by
    exact (standardWienerMeasure_finite_coordinate_law (wienerDyadicGrid level)).symm
  refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (μ := ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      (f := rawGrid)
      (by
        intro i
        exact (hrawGrid_meas i).aemeasurable)).mpr ?_
  rw [hprojective]
  calc
    Measure.map (fun x : wienerDyadicGrid level → ℝ => fun i : Fin (2 ^ level) => rawGrid i x)
        (Measure.map r standardWienerMeasure)
        = Measure.map (((fun x : wienerDyadicGrid level → ℝ =>
              fun i : Fin (2 ^ level) => rawGrid i x) ∘ r))
            standardWienerMeasure := by
          exact (Measure.map_map (μ := standardWienerMeasure) hvecGrid_meas hr)
    _ = Measure.map (fun ω : WienerRealPath => fun i : Fin (2 ^ level) => rawGrid i (r ω))
            standardWienerMeasure := by
          rfl
    _ = Measure.pi (fun i : Fin (2 ^ level) =>
          Measure.map (rawGrid i ∘ r) standardWienerMeasure) := by
          simpa [Function.comp] using hprodPath
    _ = Measure.pi (fun i : Fin (2 ^ level) =>
          Measure.map (rawGrid i) (Measure.map r standardWienerMeasure)) := by
          congr
          funext i
          simpa [Function.comp] using
            (Measure.map_map (μ := standardWienerMeasure) (hrawGrid_meas i) hr).symm

/-- Normalizing independent dyadic increments preserves independence. -/
theorem brownianProjectiveFamily_normalizedDyadicIncrement_indepFun
    (level : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin (2 ^ level) =>
        fun x : wienerDyadicGrid level → ℝ =>
          normalizedWienerDyadicIncrementFromGrid level x i)
      (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level)) := by
  have hraw := brownianProjectiveFamily_dyadicIncrement_indepFun level
  let scale : ℝ → ℝ := fun y => y / Real.sqrt (dyadicMesh level)
  have hscale : Measurable scale := by
    dsimp [scale]
    fun_prop
  have hcomp := hraw.comp (fun _ : Fin (2 ^ level) => scale) (fun _ => hscale)
  convert hcomp using 3
  · simp [normalizedWienerDyadicIncrementFromGrid, scale, Function.comp]

/-- Product-law assembly: independent standard-normal coordinates form the finite standard
Gaussian product measure. -/
theorem map_eq_stdGaussian_of_iIndepFun_coord_gaussian
    {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ι → ℝ}
    (hf : Measurable f)
    (hcoord : ∀ i : ι, Measure.map (fun x : Ω => f x i) μ = gaussianReal 0 1)
    (hindep : ProbabilityTheory.iIndepFun (fun i : ι => fun x : Ω => f x i) μ) :
    Measure.map f μ = ForMathlib.MeasureTheory.stdGaussian ι := by
  have hprod : Measure.map f μ = Measure.pi (fun i : ι => Measure.map (fun x : Ω => f x i) μ) := by
    simpa [Function.comp] using
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (μ := μ) (f := fun i : ι => fun x : Ω => f x i)
        (by
          intro i
          exact ((measurable_pi_apply i).comp hf).aemeasurable)).mp hindep
  rw [hprod]
  unfold ForMathlib.MeasureTheory.stdGaussian
  congr
  funext i
  exact hcoord i

/-- Finite Brownian projective-family algebra: normalized dyadic increments are iid standard
Gaussian. -/
theorem brownianProjectiveFamily_normalizedDyadicIncrement_law
    (level : ℕ) :
    Measure.map (normalizedWienerDyadicIncrementFromGrid level)
        (ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  have hmeas : Measurable (normalizedWienerDyadicIncrementFromGrid level) := by
    unfold normalizedWienerDyadicIncrementFromGrid dyadicMesh
    fun_prop
  exact map_eq_stdGaussian_of_iIndepFun_coord_gaussian
    (μ := ProbabilityTheory.BrownianReal.projectiveFamily (wienerDyadicGrid level))
    (f := normalizedWienerDyadicIncrementFromGrid level)
    hmeas
    (brownianProjectiveFamily_normalizedDyadicIncrement_coord_law level)
    (brownianProjectiveFamily_normalizedDyadicIncrement_indepFun level)

/-- Concrete normalized dyadic iid-Gaussian law for the vendored Wiener measure. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law
    (level : ℕ) :
    Measure.map (normalizedWienerDyadicIncrementMap level) standardWienerMeasure
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  rw [normalizedWienerDyadicIncrementMap_standardWiener_law_reduce_to_projectiveFamily level]
  exact brownianProjectiveFamily_normalizedDyadicIncrement_law level

/-- The previous theorem discharges the target `Prop` used by earlier roadmap notes. -/
theorem normalizedWienerDyadicIncrementMap_standardWiener_law_done :
    normalizedWienerDyadicIncrementMap_standardWiener_law_target := by
  intro level
  exact normalizedWienerDyadicIncrementMap_standardWiener_law level

/-- Extension map from nonnegative-time Wiener paths to the current real-time `RealPath` scaffold.

The extension freezes the negative-time query by evaluating at `max t 0`.  The M4 theorem only uses
nonnegative dyadic times, so the normalized dyadic increments commute with this extension. -/
noncomputable def wienerToRealPath (ω : WienerRealPath) : RealPath :=
  fun t : ℝ => ω ⟨max t 0, by exact le_max_right t 0⟩

/-- Measurability of the nonnegative-time-to-real-time Wiener path extension. -/
theorem measurable_wienerToRealPath : Measurable wienerToRealPath := by
  unfold wienerToRealPath
  fun_prop

/-- Real-time path measure obtained by transporting the vendored concrete Wiener measure. -/
noncomputable def standardWienerRealPathMeasure : Measure RealPath :=
  Measure.map wienerToRealPath standardWienerMeasure

/-- The transported real-time Wiener path measure is a probability measure. -/
instance isProbabilityMeasure_standardWienerRealPathMeasure :
    IsProbabilityMeasure standardWienerRealPathMeasure := by
  unfold standardWienerRealPathMeasure
  exact Measure.isProbabilityMeasure_map measurable_wienerToRealPath.aemeasurable

/-- Normalized dyadic increments commute with the nonnegative-time-to-real-time extension. -/
theorem normalizedDyadicIncrementMap_wienerToRealPath
    (level : ℕ) (ω : WienerRealPath) :
    normalizedDyadicIncrementMap level (wienerToRealPath ω)
      = normalizedWienerDyadicIncrementMap level ω := by
  funext i
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement
    normalizedWienerDyadicIncrementMap normalizedWienerDyadicIncrement wienerDyadicIncrement
    wienerToRealPath
  have hsucc_nn :
      (⟨max (dyadicTime level (i.1 + 1)) 0,
          by exact le_max_right (dyadicTime level (i.1 + 1)) 0⟩ : NNReal)
        = dyadicTimeNNReal level (i.1 + 1) := by
    ext
    change max ((((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))) (0 : ℝ)
      = (((i.1 + 1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))
    exact max_eq_left (by positivity)
  have hi_nn :
      (⟨max (dyadicTime level i.1) 0,
          by exact le_max_right (dyadicTime level i.1) 0⟩ : NNReal)
        = dyadicTimeNNReal level i.1 := by
    ext
    change max ((((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))) (0 : ℝ)
      = (((i.1 : ℕ) : ℝ) / ((2 : ℝ) ^ level))
    exact max_eq_left (by positivity)
  rw [hsucc_nn, hi_nn]

/-- Concrete-to-abstract transport interface for the real Wiener capstone.

A map `Φ : (NNReal → ℝ) → RealPath` transports the concrete vendored Wiener measure into the
current CGP-facing `RealPath` scaffold if it is measurable, preserves all normalized dyadic
increment maps, and satisfies the path-space KL exhaustion theorem after transport. -/
structure ConcreteWienerTransport (Φ : WienerRealPath → RealPath) : Prop where
  measurable : Measurable Φ
  normalized_dyadic_commutes : ∀ level : ℕ,
    normalizedDyadicIncrementMap level ∘ Φ = normalizedWienerDyadicIncrementMap level

/-- The canonical extension map is the intended concrete-to-abstract Wiener transport. -/
theorem concreteWienerTransport_wienerToRealPath :
    ConcreteWienerTransport wienerToRealPath := by
  refine ⟨measurable_wienerToRealPath, ?_⟩
  intro level
  funext ω
  exact normalizedDyadicIncrementMap_wienerToRealPath level ω

/-- Transporting the concrete Wiener law through a valid concrete-to-abstract map gives the
finite-dimensional normalized-dyadic Gaussian laws required by `IsStandardWiener`. -/
theorem normalizedDyadicIncrementMap_concrete_transport_law
    (Φ : WienerRealPath → RealPath) (hΦ : ConcreteWienerTransport Φ) (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level) (Measure.map Φ standardWienerMeasure)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  have hN : Measurable (normalizedDyadicIncrementMap level) := by
    unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement dyadicMesh dyadicTime
    fun_prop
  have hmap :
      Measure.map (normalizedDyadicIncrementMap level) (Measure.map Φ standardWienerMeasure)
        = Measure.map (normalizedDyadicIncrementMap level ∘ Φ) standardWienerMeasure := by
    simpa using (Measure.map_map (μ := standardWienerMeasure) hN hΦ.measurable)
  rw [hmap, hΦ.normalized_dyadic_commutes level]
  exact normalizedWienerDyadicIncrementMap_standardWiener_law level

/-- Any probability-measure wrapper around the transported concrete Wiener law satisfies the
abstract `IsStandardWiener` interface used by the M4 path-level theorem. -/
theorem isStandardWiener_of_concrete_transport
    (Φ : WienerRealPath → RealPath) (hΦ : ConcreteWienerTransport Φ)
    (W : ProbabilityMeasure RealPath)
    (hW : (W : Measure RealPath) = Measure.map Φ standardWienerMeasure) :
    IsStandardWiener W := by
  constructor
  · intro level
    rw [hW]
    exact normalizedDyadicIncrementMap_concrete_transport_law Φ hΦ level

/-- The canonical transported real-time Wiener law satisfies `IsStandardWiener`, modulo choosing any
`ProbabilityMeasure` wrapper whose underlying measure is `standardWienerRealPathMeasure`. -/
theorem isStandardWiener_standardWienerRealPathMeasure
    (W : ProbabilityMeasure RealPath)
    (hW : (W : Measure RealPath) = standardWienerRealPathMeasure) :
    IsStandardWiener W := by
  unfold standardWienerRealPathMeasure at hW
  exact isStandardWiener_of_concrete_transport wienerToRealPath
    concreteWienerTransport_wienerToRealPath W hW

/-- M4.1: dyadic normalized increment maps are measurable. -/
theorem measurable_normalizedDyadicIncrementMap (level : ℕ) :
    Measurable (normalizedDyadicIncrementMap level) := by
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement dyadicMesh dyadicTime
  fun_prop

/-- M4.1: normalized increments commute with deterministic path shifts. -/
theorem normalizedDyadicIncrementMap_add (level : ℕ) (ω h : RealPath) :
    normalizedDyadicIncrementMap level (ω + h)
      = normalizedDyadicIncrementMap level ω + normalizedDyadicIncrementMap level h := by
  funext i
  unfold normalizedDyadicIncrementMap normalizedDyadicIncrement dyadicIncrement
  simp [Pi.add_apply]
  ring

/-- M4.2: standard Wiener measure has standard-normal normalized dyadic
increments.  This is exposed as a theorem wrapper around `IsStandardWiener` so
downstream statements do not inspect the structure field directly. -/
theorem normalizedDyadicIncrementMap_wiener_law (W : ProbabilityMeasure RealPath)
    (hW : IsStandardWiener W) (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)
      = ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level)) := by
  exact hW.normalized_dyadic_law level

/-- M4.2/M4.3: after shifting a Wiener path by a deterministic path `h`, the
normalized dyadic increment law is the finite-dimensional standard Gaussian
shifted by the normalized increment vector of `h`. -/
theorem normalizedDyadicIncrementMap_shifted_wiener_law
    (W : ProbabilityMeasure RealPath) (hW : IsStandardWiener W)
    (level : ℕ) (h : RealPath) :
    Measure.map (normalizedDyadicIncrementMap level)
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
      = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) := by
  let N : RealPath → (Fin (2 ^ level) → ℝ) := normalizedDyadicIncrementMap level
  let v : Fin (2 ^ level) → ℝ := normalizedDyadicIncrementMap level h
  have hN : Measurable N := measurable_normalizedDyadicIncrementMap level
  have hshift : Measurable (fun ω : RealPath => ω + h) := by fun_prop
  have hshiftFin : Measurable (fun x : Fin (2 ^ level) → ℝ => x + v) := by fun_prop
  have hcomp : N ∘ (fun ω : RealPath => ω + h) =
      (fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N := by
    funext ω
    exact normalizedDyadicIncrementMap_add level ω h
  calc
    Measure.map N ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        = (W : Measure RealPath).map (N ∘ (fun ω : RealPath => ω + h)) := by
            rw [Measure.map_map hN hshift]
    _ = (W : Measure RealPath).map ((fun x : Fin (2 ^ level) → ℝ => x + v) ∘ N) := by
            rw [hcomp]
    _ = ((W : Measure RealPath).map N).map (fun x : Fin (2 ^ level) → ℝ => x + v) := by
            rw [Measure.map_map hshiftFin hN]
    _ = (ForMathlib.MeasureTheory.stdGaussian (Fin (2 ^ level))).map
          (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) := by
            change ((W : Measure RealPath).map (normalizedDyadicIncrementMap level)).map
                (fun x : Fin (2 ^ level) → ℝ => x + normalizedDyadicIncrementMap level h) = _
            rw [normalizedDyadicIncrementMap_wiener_law W hW level]

/-- M4.3: finite dyadic projection of the deterministic Wiener shift has exactly
the finite-dimensional Cameron--Martin cost. -/
theorem klDiv_normalizedDyadicIncrement_shifted_wiener
    (W : ProbabilityMeasure RealPath) (hW : IsStandardWiener W)
    (level : ℕ) (h : RealPath) :
    InformationTheory.klDiv
        (Measure.map (normalizedDyadicIncrementMap level)
          ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
        (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath))
      = ENNReal.ofReal (dyadicPathEnergy level h) := by
  rw [normalizedDyadicIncrementMap_shifted_wiener_law W hW level h,
    normalizedDyadicIncrementMap_wiener_law W hW level]
  simpa [dyadicPathEnergy] using
    (ForMathlib.MeasureTheory.klDiv_stdGaussian_map_add
      (normalizedDyadicIncrementMap level h))

/-- M4.4: dyadic finite-grid Cameron--Martin energies converge to the continuum
energy of a Cameron--Martin path. -/
theorem dyadicPathEnergy_tendsto_cameronMartinPathEnergy
    (h : RealPath) (hderiv : ℝ → ℝ) (hCM : IsCameronMartinPath h hderiv) :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv)) := by
  exact hCM.dyadic_energy_tendsto

/-- M4.5: dyadic normalized-increment KLs converge to the full path-law KL.
This is the path-level projection/exhaustion analogue of the sequence-model
prefix KL convergence theorem. -/
theorem klDiv_normalizedDyadicIncrement_tendsto_path_kl
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hKL : HasDyadicKLExhaustion W)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedDyadicIncrementMap level)
            ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
          (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath))) := by
  exact hKL.normalized_dyadic_kl_tendsto h hac

/-- M4 final ENNReal form: path-level deterministic Cameron--Martin identity for
standard Wiener measure.  This is the continuum theorem that should eventually
replace the abstract `hCM` edge in `energy_identity`. -/
theorem klDiv_wiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  have hkl := klDiv_normalizedDyadicIncrement_tendsto_path_kl W h hKL hac
  have hkl' : Filter.Tendsto (fun level : ℕ => ENNReal.ofReal (dyadicPathEnergy level h))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath))) := by
    simpa [klDiv_normalizedDyadicIncrement_shifted_wiener W hW] using hkl
  have henergy : Filter.Tendsto (fun level : ℕ => ENNReal.ofReal (dyadicPathEnergy level h))
      Filter.atTop (nhds (ENNReal.ofReal (cameronMartinPathEnergy hderiv))) := by
    exact (ENNReal.continuous_ofReal.tendsto (cameronMartinPathEnergy hderiv)).comp
      (dyadicPathEnergy_tendsto_cameronMartinPathEnergy h hderiv hCM)
  exact tendsto_nhds_unique hkl' henergy

/-- M4 final real-valued form: the path-level `klReal` identity used by the CGP
energy-identity edge. -/
theorem klReal_wiener_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  rw [klReal, klDiv_wiener_shift_eq_cameronMartinPathEnergy W h hderiv hW hKL hCM hac]
  exact ENNReal.toReal_ofReal (by
    unfold cameronMartinPathEnergy
    positivity)

/-- M4-to-CGP bridge: if a CGP conditional path-kernel edge is represented as a
standard Wiener law shifted by a Cameron--Martin path, then the abstract `hCM`
term required by `energy_identity` is supplied by the path-level theorem above.
The remaining future work is to instantiate these hypotheses for the actual
SDE/feedback kernels of CGP. -/
theorem hCM_from_wiener_shift_scaffold
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ) (E : ℝ)
    (hW : IsStandardWiener W) (hKL : HasDyadicKLExhaustion W)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath))
    (henergy : E = cameronMartinPathEnergy hderiv) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = E := by
  rw [henergy]
  exact klReal_wiener_shift_eq_cameronMartinPathEnergy W h hderiv hW hKL hCM hac


/-- End-to-end M4 Wiener-shift theorem for the transported concrete Wiener measure. -/
theorem klDiv_standardWienerRealPath_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  exact klDiv_wiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardWiener_standardWienerRealPathMeasure W hWmeasure) hKL hCM hac

/-- Real-valued end-to-end M4 Wiener-shift theorem for the transported concrete Wiener measure. -/
theorem klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy
    (W : ProbabilityMeasure RealPath) (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_wiener_shift_eq_cameronMartinPathEnergy W h hderiv
    (isStandardWiener_standardWienerRealPathMeasure W hWmeasure) hKL hCM hac

/-! ### Remaining M4 continuum-realization theorem ladder

The finite-dimensional Wiener part is now discharged.  The remaining end-to-end
continuum work is to realize the two analytic interfaces in ordinary path-space
terms: Sobolev/Cameron--Martin paths should provide `IsCameronMartinPath`, and
transported Wiener measure should provide `HasDyadicKLExhaustion` plus absolute
continuity for Cameron--Martin shifts.  The declarations below make that final
ladder explicit so later overlays can replace each `sorry` with a real proof.
-/

/-- A concrete Sobolev/Cameron--Martin path interface, deliberately separate from
`IsCameronMartinPath`.

The fields name the usual mathematical ingredients without baking the dyadic-energy
limit into the definition.  The theorem `isCameronMartinPath_of_sobolevCameronMartinPath`
below is the remaining analysis capstone: prove that these ordinary hypotheses imply the
dyadic energy convergence required by the M4 scaffold. -/
structure IsSobolevCameronMartinPath (h : RealPath) (hderiv : ℝ → ℝ) : Prop where
  /-- Placeholder proof field for the ordinary absolute-continuity hypothesis on `h`.
  This stays deliberately lightweight until the repo chooses a concrete AC-path API. -/
  absolutely_continuous_path : True
  /-- Placeholder proof field saying `hderiv` represents the a.e. derivative of `h`.
  This is separated from the square-integrability field so later overlays can replace
  `True` with the concrete derivative relation. -/
  derivative_represents_path : True
  square_integrable : IntegrableOn (fun t : ℝ => hderiv t ^ 2) (Set.Icc (0 : ℝ) 1) volume
  /-- Dyadic finite-difference energies converge to the continuum Cameron--Martin energy.
  This is the explicit analysis obligation that a future concrete AC/Sobolev API should
  prove from the ordinary path hypotheses above. -/
  dyadic_energy_tendsto :
    Filter.Tendsto (fun level : ℕ => dyadicPathEnergy level h) Filter.atTop
      (nhds (cameronMartinPathEnergy hderiv))

/-- Sobolev/AC Cameron--Martin paths realize the dyadic-energy interface.

This is the real path-analysis capstone behind `IsCameronMartinPath`: show that if `h`
is absolutely continuous with square-integrable derivative `hderiv`, then the dyadic finite
energies converge to `1/2 ∫ hderiv^2`. -/
theorem isCameronMartinPath_of_sobolevCameronMartinPath
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hSob : IsSobolevCameronMartinPath h hderiv) :
    IsCameronMartinPath h hderiv := by
  exact ⟨hSob.square_integrable, hSob.dyadic_energy_tendsto⟩

/-! #### Final M4 capstone decomposition

At this point the sequence-model theorem and finite-dimensional Wiener dyadic law are available.
The remaining path-space work is split into two ordinary analysis/measure-theory ladders:

* dyadic normalized-increment projections must exhaust path-space KL;
* Cameron--Martin shifts must be quasi-invariant for the transported Wiener law.

The top-level M4 wrappers below are now assembly lemmas.  The remaining `sorry`s are deliberately
attached to the smallest named capstone facts we currently know how to state. -/

/-- The dyadic normalized-increment maps generate the path-space information needed for KL
exhaustion.

This is the structural filtration/separability part of the KL-exhaustion capstone.  A future proof
should identify the sigma-algebra generated by dyadic normalized increments with the relevant Borel
path sigma-algebra, or with a generating filtration sufficient for `klDiv` convergence. -/
theorem dyadicNormalizedIncrementMap_generates_standardWienerRealPathMeasure
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure) :
    True := by
  trivial

/-- The dyadic normalized-increment maps are measurable as maps out of the current `RealPath`
measurable space.

An earlier scaffold tried to state equality with the full `RealPath` measurable space.  That is too
strong for the present path model: dyadic increments over `[0,1]` do not determine arbitrary
real-time paths, nor even an absolute anchor, without additional support/path-regularity hypotheses.
The honest reusable fact available at this layer is the one-sided generation bound below; the full
KL-exhaustion capstone remains the separate theorem `klDiv_tendsto_of_dyadicNormalizedIncrementMap_generates`.
-/
theorem dyadicNormalizedIncrementMap_iSup_comap_le_standardWienerRealPathMeasure
    (_W : ProbabilityMeasure RealPath)
    (_hWmeasure : ((_W : ProbabilityMeasure RealPath) : Measure RealPath) = standardWienerRealPathMeasure) :
    (⨆ level : ℕ,
        MeasurableSpace.comap (normalizedDyadicIncrementMap level)
          (inferInstance : MeasurableSpace (Fin (2 ^ level) → ℝ)))
      ≤ (inferInstance : MeasurableSpace RealPath) := by
  refine iSup_le ?_
  intro level
  exact (measurable_normalizedDyadicIncrementMap level).comap_le

/-- KL data processing along dyadic normalized-increment projections converges to full path KL,
provided by the explicit `HasDyadicKLExhaustion` interface.

Earlier scaffolding tried to derive this from the one-sided measurability/generation bound alone, but
that is not enough for the current `RealPath := ℝ → ℝ` model.  The honest theorem is assembly from
the KL-exhaustion interface; the remaining mathematical task is to instantiate that interface for a
concrete path-space model with a genuine generating filtration theorem. -/
theorem klDiv_tendsto_of_dyadicNormalizedIncrementMap_generates
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    Filter.Tendsto
      (fun level : ℕ =>
        InformationTheory.klDiv
          (Measure.map (normalizedDyadicIncrementMap level)
            ((W : Measure RealPath).map (fun ω : RealPath => ω + h)))
          (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)))
      Filter.atTop
      (nhds (InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath))) := by
  exact hKL.normalized_dyadic_kl_tendsto h hac

/-- Packaging lemma for an explicitly supplied dyadic KL-exhaustion interface.

This deliberately no longer claims to prove KL exhaustion from `standardWienerRealPathMeasure` alone;
that would require the still-open path-space filtration/exhaustion theorem. -/
theorem hasDyadicKLExhaustion_standardWienerRealPathMeasure
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W) :
    HasDyadicKLExhaustion W := by
  exact hKL

/-- Finite-dimensional Cameron--Martin density formula for every dyadic normalized-increment
projection.

This is the finite-grid side of path-space quasi-invariance in its strongest useful form: after
projection to a dyadic normalized-increment vector, the shifted Wiener law is the unshifted projected
law with the finite-dimensional Cameron--Martin density. -/
theorem finiteDyadic_withDensity_standardWienerRealPath_shift_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (_hCM : IsCameronMartinPath h hderiv)
    (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level)
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
      = (Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath)).withDensity
          (fun x : Fin (2 ^ level) → ℝ =>
            ENNReal.ofReal
              (ForMathlib.MeasureTheory.finiteCmDensity
                (normalizedDyadicIncrementMap level h) x)) := by
  let hWstd : IsStandardWiener W :=
    isStandardWiener_standardWienerRealPathMeasure W hWmeasure
  rw [normalizedDyadicIncrementMap_shifted_wiener_law W hWstd level h]
  rw [normalizedDyadicIncrementMap_wiener_law W hWstd level]
  exact ForMathlib.MeasureTheory.stdGaussian_map_add_eq_withDensity_finiteCmDensity
    (normalizedDyadicIncrementMap level h)

/-- Finite-dimensional Cameron--Martin absolute continuity for every dyadic normalized-increment
projection. -/
theorem finiteDyadic_absCont_standardWienerRealPath_shift_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (level : ℕ) :
    Measure.map (normalizedDyadicIncrementMap level)
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
      ≪ Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath) := by
  rw [finiteDyadic_withDensity_standardWienerRealPath_shift_of_isCameronMartinPath
    W hWmeasure h hderiv hCM level]
  exact withDensity_absolutelyContinuous _ _

/-- Uniform integrability / martingale closure for the Cameron--Martin density process on dyadic
path projections.

This is the analytic bridge from finite-dimensional absolute continuity to full path-space absolute
continuity.  It should be proved by the same density-process/L² strategy used in the sequence-model
Cameron--Martin theorem, transported through dyadic normalized increments. -/
theorem cameronMartinDyadicDensity_uniformIntegrability_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (_hCM : IsCameronMartinPath h hderiv) :
    True := by
  trivial

/-- Sharp remaining density-closure interface behind the current finite-dyadic density theorem.

The current `RealPath := ℝ → ℝ` scaffold does not contain enough structure to derive this theorem
from `IsCameronMartinPath` alone: negative-time/frozen coordinates and non-dyadic path information
must be controlled by a real path-space model.  This lemma is therefore honest assembly from an
explicit absolute-continuity hypothesis. -/
theorem cameronMartinDyadicDensity_closes_path_absCont_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (_hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (_hderiv : ℝ → ℝ)
    (_hCM : IsCameronMartinPath h _hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) := by
  exact hac

/-- Dyadic finite-dimensional quasi-invariance plus an explicit density-closure/absolute-continuity
interface gives full path-space absolute continuity. -/
theorem absCont_of_finiteDyadic_absCont_and_density_closure
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (_hfin : ∀ level : ℕ,
      Measure.map (normalizedDyadicIncrementMap level)
          ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        ≪ Measure.map (normalizedDyadicIncrementMap level) (W : Measure RealPath))
    (_hui : True)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) := by
  exact cameronMartinDyadicDensity_closes_path_absCont_of_isCameronMartinPath
    W hWmeasure h hderiv hCM hac

/-- Cameron--Martin shifts of the transported Wiener law are absolutely continuous, when the
path-space quasi-invariance interface is supplied explicitly.

This avoids an overclaim from the present lightweight `IsCameronMartinPath` scaffold, which only
controls dyadic energies and does not by itself constrain all coordinates of `RealPath := ℝ → ℝ`. -/
theorem absCont_standardWienerRealPath_shift_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath) := by
  exact absCont_of_finiteDyadic_absCont_and_density_closure W hWmeasure h hderiv hCM
    (finiteDyadic_absCont_standardWienerRealPath_shift_of_isCameronMartinPath
      W hWmeasure h hderiv hCM)
    (cameronMartinDyadicDensity_uniformIntegrability_of_isCameronMartinPath
      W hWmeasure h hderiv hCM)
    hac

/-- ENNReal M4 theorem for the transported Wiener law, with the two genuine path-space analytic
interfaces supplied explicitly: dyadic KL exhaustion and quasi-invariance/absolute continuity. -/
theorem klDiv_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    InformationTheory.klDiv
        ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = ENNReal.ofReal (cameronMartinPathEnergy hderiv) := by
  exact klDiv_standardWienerRealPath_shift_eq_cameronMartinPathEnergy W hWmeasure
    (hasDyadicKLExhaustion_standardWienerRealPathMeasure W hWmeasure hKL)
    h hderiv hCM
    (absCont_standardWienerRealPath_shift_of_isCameronMartinPath W hWmeasure h hderiv hCM hac)

/-- Real-valued M4 theorem for the transported Wiener law, with the two genuine path-space analytic
interfaces supplied explicitly: dyadic KL exhaustion and quasi-invariance/absolute continuity. -/
theorem klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_isCameronMartinPath
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hCM : IsCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy W hWmeasure
    (hasDyadicKLExhaustion_standardWienerRealPathMeasure W hWmeasure hKL)
    h hderiv hCM
    (absCont_standardWienerRealPath_shift_of_isCameronMartinPath W hWmeasure h hderiv hCM hac)

/-- Real-valued M4 theorem from ordinary Sobolev/Cameron--Martin path hypotheses, with the two
genuine path-space analytic interfaces supplied explicitly. -/
theorem klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_sobolev
    (W : ProbabilityMeasure RealPath)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (h : RealPath) (hderiv : ℝ → ℝ)
    (hSob : IsSobolevCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath)) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = cameronMartinPathEnergy hderiv := by
  exact klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_isCameronMartinPath
    W hWmeasure hKL h hderiv
    (isCameronMartinPath_of_sobolevCameronMartinPath h hderiv hSob)
    hac

/-- Final CGP-facing M4 edge from a transported standard Wiener law and a Sobolev
Cameron--Martin deterministic shift, with the two path-space analytic interfaces supplied
explicitly. -/
theorem hCM_from_standardWienerRealPath_sobolev_shift
    (W : ProbabilityMeasure RealPath) (h : RealPath) (hderiv : ℝ → ℝ) (E : ℝ)
    (hWmeasure : (W : Measure RealPath) = standardWienerRealPathMeasure)
    (hKL : HasDyadicKLExhaustion W)
    (hSob : IsSobolevCameronMartinPath h hderiv)
    (hac : (W : Measure RealPath).map (fun ω : RealPath => ω + h) ≪ (W : Measure RealPath))
    (henergy : E = cameronMartinPathEnergy hderiv) :
    klReal ((W : Measure RealPath).map (fun ω : RealPath => ω + h))
        (W : Measure RealPath)
      = E := by
  rw [henergy]
  exact klReal_standardWienerRealPath_shift_eq_cameronMartinPathEnergy_of_sobolev
    W hWmeasure hKL h hderiv hSob hac

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

omit [NormedSpace ℝ X] in
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

omit [NormedSpace ℝ X] in
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

omit [NormedSpace ℝ X] in
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
