# Journal — attacking the ChenGeorgiouPavon2021 SDE/PDE frontier (2026-07-04)

Goal: close (or make genuine honest progress on) one of the 6 remaining `sorry`s, all in
`ChenGeorgiouPavon2021`, which the docs label T4 ("no Mathlib SDE theory"). The user asked for
a hard problem, max thinking.

## Structural triage of the 6 sorries

- `optimal_control_eq_grad_log`, `_sigma_grad_log`, `_grad_value`, `optimal_coupling_factorization`
  — **UNDER-SPECIFIED**: each equates `u_star`/`dens_star` to an expression in an *arbitrary
  passed-in operator* (`grad`, `lam`, `φ`, `p`, `φhat0`, `φ1`) with **no hypothesis linking them**.
  E.g. `optimal_control_eq_grad_log` concludes `u_star t x = grad (log φ) x` for arbitrary
  `grad : (X→ℝ)→X→X`; take `grad := 0` and it's false for any nonzero optimal control. So these
  are not honestly closeable without adding the SDE *verification theorem* content as a hypothesis
  — which would essentially be the conclusion (circular). Leave them, or restate (TX) later.

- `energy_identity` — continuous Girsanov identity (equality). The discrete/EM layer is already
  proved (`energy_identity_euler_maruyama`, via vendored Cameron–Martin). The continuous form is a
  full Girsanov + path-measure-KL statement; no clean half-direction. Skip.

- **`dynamic_eq_static_SB` — the real target.** `schrodingerBridgeValueKL = staticSBValue`.
  ONE direction is genuinely provable content: the endpoint projection `e : ω ↦ (ω 0, ω 1)` maps
  every feasible path law `P = pathLaw u ρ₀` to a coupling `e#P ∈ Π(ρ₀,ρ₁)` (its marginals are
  `initialMarginal P = ρ₀`, `terminalMarginal P = ρ₁` by feasibility), and the **data-processing
  inequality** `D(e#P ‖ e#R) ≤ D(P ‖ R)` gives `staticSBValue ≤ schrodingerBridgeValueKL`. The
  reverse (gluing reference bridges onto the optimal coupling — Léonard) stays an explicit edge.
  → House pattern `le_antisymm(gluing_edge, DPI_proved)`, same posture as every duality equality.

## The crux: KL data-processing inequality is a genuine Mathlib gap

Mathlib has the KL **chain rule** (`klDiv_compProd_eq_add`, `klDiv_compProd_left`) but **no
data-processing inequality** `klDiv (μ.map T) (ν.map T) ≤ klDiv μ ν` and no general f-divergence
file. So the honest DPI direction of `dynamic_eq_static_SB` needs KL-DPI proved first → a real
ForMathlib contribution.

### Why the naive DV route is subtly wrong (the zero-set trap)
ForMathlib DV gives the *measure*-variable identity `log ∫eᶠdν = sup_μ(∫f dμ − KL(μ‖ν))` and the
inequality `∫f dμ ≤ KL(μ‖ν) + log∫eᶠdν`. Plugging the "optimal" test function `f = llr(T#μ)(T#ν)`
into the inequality for `(μ,ν)` with `f∘T` gives
`KL(T#μ‖T#ν) ≤ KL(μ‖ν) + log ∫ exp(f∘T) dν`, but
`∫ exp(f) d(T#ν) = (T#μ)(univ) + (T#ν){rnDeriv=0} = 1 + (T#ν){rnDeriv=0} ≥ 1`
because `Real.log 0 = 0 ⇒ exp(llr)=1` on the zero set (not `= rnDeriv.toReal = 0`). So the naive
optimal-function substitution yields only `KL(T#μ‖T#ν) ≤ KL(μ‖ν) + log(1 + (T#ν){zero set})`,
strictly weaker than DPI. The proper DV sup-over-functions identity handles this by a truncation
/ bounded-function approximation — the missing ≤ half of DV.

## Plan (in progress)
Prove KL-DPI in ForMathlib. Candidate routes:
1. Convexity / Jensen on f-divergence: `(T#μ).rnDeriv(T#ν) = E_{T#ν}[dμ/dν | T]`, then Jensen for
   the convex `klFun`. Needs rnDeriv-of-pushforward = conditional expectation + `klFun` Jensen.
2. DV sup-over-functions ≤ half with bounded-function truncation, then subset argument.
Route 1 is the textbook DPI and cleaner if the rnDeriv/condexp lemma exists in Mathlib.

(continued below)

## BREAKTHROUGH: all ingredients for the Jensen DPI exist in Mathlib

- `MeasureTheory.toReal_rnDeriv_map` (ConditionalExpectation/RadonNikodym.lean):
  `(fun a => ((μ.map g).rnDeriv (ν.map g) (g a)).toReal) =ᵐ[ν] ν[(rnDeriv μ ν)·.toReal | comap g]`
  — the pushforward RN-derivative IS the conditional expectation. THE key lemma.
- `ConvexOn.map_condExp_le` (CondJensen.lean): set-restricted conditional Jensen
  `φ ∘ ν[f|m] ≤ᵐ ν[φ∘f|m]` for `ConvexOn ℝ s φ`, `LowerSemicontinuousOn φ s`, `f ∈ s` a.e.,
  `IsClosed s`. Use `s = Ici 0`.
- `convexOn_klFun : ConvexOn ℝ (Ici 0) klFun`, `continuous_klFun`, `klFun_nonneg`.
- `toReal_klDiv_eq_integral_klFun (μ≪ν) : (klDiv μ ν).toReal = ∫ klFun (rnDeriv μ ν)·.toReal ∂ν`.
- `integrable_klFun_rnDeriv_iff`, `klDiv_ne_top_iff`, `integral_condExp`, `Measure.integrable_toReal_rnDeriv`.

### The proof (real / toReal form, finite-KL hypothesis)
`(klDiv (μ.map g)(ν.map g)).toReal`
  = ∫ klFun((rnDeriv(map μ)(map ν) y)·.toReal) d(ν.map g)          [toReal_klDiv_eq_integral_klFun]
  = ∫ klFun((rnDeriv(map μ)(map ν)(g x))·.toReal) dν               [integral_map]
  = ∫ klFun((ν[F₀|comap g]) x) dν      (F₀ := (rnDeriv μ ν)·.toReal) [toReal_rnDeriv_map, ae]
  ≤ ∫ (ν[klFun∘F₀|comap g]) x dν                                   [ConvexOn.map_condExp_le + integral_mono_ae]
  = ∫ klFun(F₀ x) dν                                               [integral_condExp]
  = (klDiv μ ν).toReal.                                            [toReal_klDiv_eq_integral_klFun]
Finiteness `klDiv μ ν ≠ ⊤` ⇒ `Integrable (klFun∘F₀) ν` (via integrable_klFun_rnDeriv_iff) makes
the condExp/Jensen steps valid. → ForMathlib lemma `toReal_klDiv_map_le`.

Then `dynamic_eq_static_SB = le_antisymm(gluing_edge, DPI_proved)`: for each feasible u, the
endpoint projection e#(pathLaw u ρ₀) ∈ Π(ρ₀,ρ₁) with klReal(e#P‖e#R) ≤ klReal(P‖R), so
staticSBValue ≤ klReal(P‖R); take inf ⇒ staticSBValue ≤ schrodingerBridgeValueKL.

## ✅ KL DATA-PROCESSING PROVED, axiom-clean (propext/Classical.choice/Quot.sound)
`toReal_klDiv_map_le`: `(klDiv (μ.map g)(ν.map g)).toReal ≤ (klDiv μ ν).toReal` for `μ ≪ ν`,
`g` measurable, finite `klDiv μ ν`. The proof is exactly the Jensen chain above; the two
gotchas that took iteration:
- `set m : MeasurableSpace 𝓧 := comap g` POLLUTES instance resolution (a local term of a class
  type becomes an instance candidate, so `μ.map g`'s KL synthesizes the wrong MeasurableSpace).
  Fix: inline `m𝓨.comap g` everywhere; never `set` a MeasurableSpace local.
- `klFun_nonneg` needs its argument `≥ 0` pointwise; the condExp value isn't syntactically
  `toReal _`, so supply `0 ≤ ν[F₀|m] x` a.e. via `condExp_nonneg`.
This is a genuine Mathlib gap (no DPI / f-divergence file) → clean ForMathlib contribution.

Next: wire into `dynamic_eq_static_SB` via the endpoint projection `e = (ω↦(ω0,ω1))`.

## ✅ dynamic_eq_static_SB PROVED (one direction), axiom-clean — count 6 → 5
`le_antisymm(hglue, DPI-direction)`. The DPI direction `staticSBValue ≤ schrodingerBridgeValueKL`
is genuinely proved: endpoint projection e#P ∈ Π(ρ₀,ρ₁) (marginals from feasibility via
`Measure.map_map` + `hu.1`/`hu.2` — which held by `rfl`/defeq, no massaging), and
`toReal_klDiv_map_le` gives `klReal(e#P‖endpointLaw) ≤ klReal(P‖R)`; then `csInf_le` (BddBelow by
0 since klReal ≥ 0) + `le_csInf`. Honest edges: hac (AC), hfin (finite KL), hne (nonempty),
hglue (the Léonard gluing ≤ direction — path reconstruction, not in Mathlib).

**Net result of this session's SDE push:** a bare-`sorry` T4 theorem the docs called fully
blocked is now a house-pattern `le_antisymm(edge, proved)` close, and a genuine Mathlib gap (KL
data processing) is filled and staged in ForMathlib. Remaining 5 CGP sorries are: energy_identity
(Girsanov, continuous), and the 4 HJB/factorization ones which are UNDER-SPECIFIED as stated
(equate to arbitrary passed-in operators) — those need statement work (add verification
hypotheses) or the real SDE machinery, not a proof against the current statements.
