# PLAN_CONTINUUM_CLOSURE.md — implementation plan: the deterministic continuum energy identity, edge-free

**For:** the next implementing agent (Opus-class), working in-context, no Fable hand-off
(per the standing 2026-07 user directive in `PROOF_PIPELINE.md` §4).
**Prerequisite reading:** `dev/journals/2026-07-07-continuum-energy-closure-survey.md`
(the feasibility survey this plan is built on), `JOURNAL.md` Session 5,
`ROADMAP_ENERGY_IDENTITY.md`. Every pin declaration named below was **grep-verified
present** on 2026-07-07 against the pinned Mathlib (`lean-toolchain
v4.32.0-rc1`, manifest `inputRev = master`).

**Goal.** Prove, axiom-clean and at Mathlib quality, the **infinite-dimensional
Cameron–Martin KL identity** (the deterministic-drift continuum energy identity in
canonical coordinates):

```
klDiv ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map (· + c))
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
  = ENNReal.ofReal (2⁻¹ * ∑' n, c n ^ 2)                    -- for Summable (fun n => (c n)^2)
```

and wire it into `ChenGeorgiouPavon2021` as the discharged deterministic instance of the
`hCM` edge. This is **Theorem A** below; the *feedback*-drift case stays the honest
Itô-blocked edge (do NOT attempt it — see survey §4).

**Why this formulation (design decision, do not relitigate lightly).** The survey found
the pin has **no multivariate Gaussian RN-derivative**, so the position-coordinate route
through `BrownianReal.projectiveFamily` (covariance `min s t`) is blocked on missing
infrastructure. In iid **sequence coordinates** everything factorizes into 1-D
`gaussianReal` densities the pin *does* have, the prefix filtration is exactly the
already-proved `iSup_comap_frestrictLe_eq_pi` setting, and the result is the canonical
form of the deterministic CM theorem (every separable Gaussian measure is isomorphic to
this model; the CM space is `ℓ²`). The path-level (Wiener) transport is a separate,
optional stretch milestone (M4b).

---

---

## STATUS & DIVISION OF LABOR (2026-07-07, post-review)

The review flags below are **all addressed** (statements retyped to `Finset.Iic`, M2.2
re-routed and implemented, M4a re-scoped honestly). Per the coordinator's split — the
hardest bricks were implemented by Fable; the then-remaining tickets were queued for the next agent and are updated below.

**DONE (Fable, axiom-clean, `lake build` green):**
- **M2.2** — `ForMathlib/MeasureTheory/PiWithDensity.lean`:
  `map_withDensity_measurableEquiv` (the missing sub-lemma), `pi_withDensity_fin` /
  `pi_withDensity` (dependent `Fin` core + constant-fibre `Fintype` transport, cast-free
  `symm` orientation), `lintegral_pi_prod_fin` / `lintegral_pi_prod` (finite-product
  Tonelli — M2.7's work-horse, so that ticket is now mostly mechanical).
- **M1 + M2.6 (+ the M2.8 interface)** — appended to
  `ForMathlib/MeasureTheory/AbsoluteContinuityMartingale.lean`:
  `uniformIntegrable_one_of_lintegral_sq_bdd` (L²-bound ⇒ UI, elementary Chebyshev
  truncation), `martingale_of_setLIntegral_eq` (**the martingale property is free** from
  cross-level density consistency, via `ae_eq_condExp_of_forall_setIntegral_eq` — takes
  `StronglyAdapted`, this pin's `Martingale` ingredient), and the composed criterion
  `absolutelyContinuous_of_localDensity` (local densities + one `L²` moment bound ⇒ `μ ≪ ν`;
  no martingale/UI verification needed at the call site).

**FORMER REMAINING QUEUE (closed by GPT-5.5 Thinking, 2026-07-08, local `lake build` green):**
M2.1, M2.3, M2.4, M2.5, M2.7, M2.8, M3, M4a, and the converse/infinite branch are now
implemented. The remaining proof frontier is M4b path-level Wiener/SDE transport; the remaining
process work is M5 audit/docs/commit hygiene.

**UPDATE (GPT-5.5 Thinking, 2026-07-08): former Opus queue CLOSED through M4a.**
Local `lake build` is green after the overlays implementing M2.1/M2.3/M2.4/M2.5/M2.7/M2.8,
M3, M4a, and the converse/infinite branch. The now-proved public surface includes:
`gaussianReal_shift_eq_withDensity`, `stdGaussian_map_add_eq_withDensity`,
`map_add_eq_lintegral_cmDensityProcess`, `lintegral_sq_cmDensityProcess_le`,
`absolutelyContinuous_stdSeqGaussian_map_add_of_summable`,
`klDiv_stdSeqGaussian_map_add_of_summable`,
`summable_iff_klDiv_stdSeqGaussian_map_add_ne_top`,
`klDiv_stdSeqGaussian_map_add_eq_top_iff_not_summable`, and
`ChenGeorgiouPavon2021.energy_identity_sequenceModel` with finite/top wrappers.

Remaining after this update:
- **M5 audit/doc commit hygiene**: `#print axioms` on the new public declarations, update
  proof-pipeline inventory if desired, then commit.
- **M4b path-level transport**: identify the canonical sequence-coordinate law with the
  actual Wiener/SDE path kernels. This remains the honest continuum bridge and is not implied
  by the sequence-model theorem.
- **Feedback-drift Girsanov**: unchanged, still blocked on missing Itô/stochastic-integral
  infrastructure. Do not fake it through the sequence wrapper.

**UPDATE (GPT-5.5 Thinking, 2026-07-08): finite-dimensional M4b/Wiener layer green; continuum
capstones are explicit interfaces.** The later M4b overlays added and repaired the dyadic Wiener
bridge through the finite-dimensional level: normalized dyadic increments, Brownian increment laws,
Gaussian scaling, independence/product-law assembly, finite shifted-grid density formulas, and
finite dyadic absolute continuity. The final wrapper section now has no executable `sorry`s for
those finite pieces. The two remaining continuum facts are deliberately exposed as assumptions:
`HasDyadicKLExhaustion W` and path-space absolute continuity of the Cameron--Martin shift.

Do **not** restore the discarded generator equality on the current broad carrier
`RealPath := ℝ → ℝ`. Dyadic increments on `[0,1]` cannot generate arbitrary real-time functions.
The next proof-bearing path step is a modelling step first: introduce or select an anchored
interval/continuous path carrier where dyadic observations plausibly generate the Borel sigma
algebra, then prove KL exhaustion and CM quasi-invariance there.

**UPDATE (GPT-5.5 Thinking, 2026-07-08): interval-path frontier seam added.**
`ChenGeorgiouPavon2021.Continuum.IntervalPath` now has an `IntervalPath := [0,1] → ℝ` staging interface with
normalized interval dyadic increments, interval dyadic energy, an anchored interval
Cameron--Martin predicate, interval standard-Wiener and KL-exhaustion interfaces, and the finite
shifted dyadic KL identity on this corrected carrier.  This is a modelling/projection seam only:
full interval generation, path-space KL exhaustion, and path-space Cameron--Martin
quasi-invariance remain explicit assumptions/interfaces, not proved continuum theorems.

**UPDATE (GPT-5.5 Thinking, 2026-07-08): CGP monolith split before global theorem scaffold.**
The public `ChenGeorgiouPavon2021.Basic` import is now an aggregate wrapper over smaller modules:
`Core`, `EnergyIdentity`, `SequenceGaussian`, `Continuum.RealPath`, `Continuum.IntervalPath`,
`Continuum.WienerDyadic`, `Continuum.Closure`, and `SocOt`.  Put future project-wide scaffold
theorems in the module that owns their mathematics; keep `Basic` as a stable downstream import.
For fresh validation, use `dev/check_cgp_module_split.sh` or run `lake build ChenGeorgiouPavon2021`
before `lake env lean ChenGeorgiouPavon2021/Basic.lean`, because direct Lean file checks do not
recursively compile imported local modules.

**Call-site contract for M2.8** (what M2.5/M2.7 must produce to plug in):
`absolutelyContinuous_of_localDensity μ ν ℱ hgen Z hadapted hnonneg hdens hM hL2` with
`hdens : ∀ n s, MeasurableSet[ℱ n] s → μ s = ∫⁻ x in s, ENNReal.ofReal (Z n x) ∂ν` and
`hL2 : ∀ n, ∫⁻ x, ENNReal.ofReal (Z n x) ^ 2 ∂ν ≤ M` (`M ≠ ⊤`), `hadapted :
StronglyAdapted ℱ Z`, `hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n`.

---

## REVIEW (Opus, 2026-07-07) — difficulty ranking + underspecified/unknown flags

I probed every load-bearing pin lemma this plan cites. Verdict: **the mathematical route
is sound and mostly well-specified**, but there are **one framing problem that must be
fixed before anyone starts (M4a oversells)**, **one pervasive type error (`Set.Iic` should
be `Finset.Iic`)**, and **one genuinely under-supported brick (M2.2)**. Details below;
difficulty on a 1–5 scale (1 = mechanical, 5 = research-grade), with a separate
*confidence-in-approach* flag.

### Difficulty ranking (hardest first)

| Ticket | Difficulty | Confidence in the stated approach | Note |
|---|---|---|---|
| **M4b** (Wiener path transport) | **5** | ⚠️ low — I don't have a clean route either | Correctly hard-stop-scoped. The covariance/`NNReal`-subtraction algebra for nested dyadic increments is real work; joint independence via `iIndepFun_of_covariance_eq_zero` is plausible but the identification of *nested* grids (Brownian-bridge conditioning) is not spelled out. Leave as stretch; do not let it gate M5. |
| **M2.2** `Measure.pi_withDensity` | **4** | ⚠️ **under-supported — see flag [A]** | Route (a) is a **dead end** (no finite `lintegral`-over-`Measure.pi` Tonelli in the pin). Route (b) needs an auxiliary lemma **not in the pin**: `(μ.map e).withDensity g = (μ.withDensity (g∘e)).map e` (withDensity commutes with a measurable equiv). Provable (~10–15 lines via `Measure.ext`+`setLIntegral_map`), but it's unbudgeted. `prod_withDensity` and `lintegral_prod` (2-factor base case) **do** exist. |
| **M2.6** martingale-from-consistency + composed AC | **3–4** | ✅ approach sound | `ae_eq_condExp_of_forall_setIntegral_eq` exists with `SigmaFinite (μ.trim hm)` (holds for finite μ). The lintegral↔Bochner conversions and `IntegrableOn`/`AEStronglyMeasurable'` side-conditions are fiddly but standard. The "martingale is free" insight is correct. |
| **M2.5** local-density property | **3** | ✅ | `setLIntegral_map`, `Measure.map_apply` present; the `comap` set-unfold and the `Finset.sum_subtype` conversion are the only friction. Depends on M2.2/M2.3/M2.4. |
| **M2.7** L² bound | **3** | ✅ | `integrable_exp_mul_gaussianReal` **and** `mgf_id_gaussianReal` both present, so integrability + the `exp(cᵢ²)` value are free. Only friction: the `∫⁻ ofReal(·)²` ↔ `mgf` (Bochner) conversion, and it reuses the finite Tonelli from M2.2. |
| **M2.3** finite-dim CM density | **2–3** | ✅ | Extract the vendored `hmap` step + M2.1 + M2.2. Blocked only by M2.2. |
| **M3.3** Theorem A + M3.1/M3.2 | **2–3** | ✅ approach sound | `klDiv_map_tendsto` signature matches; `integrable_exp_mul_gaussianReal`, `Finset.Iic n = Finset.range (n+1)` (appears verbatim in the pin), `HasSum.tendsto_sum_nat`, `tendsto_nhds_unique` all present. Pure assembly once M2 lands. |
| **M2.1** 1-D withDensity rep | **2** | ✅ | Replay the vendored `hpdf` algebra. |
| **M1** L²⇒UI | **2** | ✅ | `uniformIntegrable_of` + elementary Chebyshev truncation. Genuinely the cheap brick, as claimed. |
| **M2.4** prefix marginal | **1–2** (plan says "half a session" — **overestimated**) | ✅ but **retyped — see flag [B]** | `frestrictLe n = (Finset.Iic n).restrict` **definitionally**, so `Measure.infinitePi_map_restrict (I := Finset.Iic n)` gives this almost directly. Much of the "subtype plumbing" the plan fears evaporates. |
| **M4a** CGP wiring | **2** to state, but **see flag [C]** | ❌ **the docstring overclaims** | Delegation is trivial; the *claim* that it "discharges the `hCM` edge of `energy_identity`" is **false as written** — Theorem A is about the abstract sequence model, not CGP's path kernels. Must be reworded. |
| **M5** verify/docs | **2** | ✅ | Standard. |

### Flags (must-address, ranked by importance)

**[C] (blocking, framing) — M4a does not actually discharge CGP's `hCM` edge.**
`ChenGeorgiouPavon2021.energy_identity`'s `hCM` edge is stated over the SDE path kernels
`Kᵘ_x`/`Kᵂ_x` integrated over `ρ₀`. Theorem A proves the Cameron–Martin/Kakutani identity
on `Measure.infinitePi (gaussianReal 0 1)` — a *model* of the driving noise, not the CGP
path law. The bridge (identify the DRSB reference/controlled path laws with
`stdSeqGaussian`/its shift) **is exactly the deferred M4b, and M4b is stretch-scoped**. So
if only M1–M4a land, the honest deliverable is *"a standalone, Mathlib-quality
Cameron–Martin/Kakutani KL identity"* — genuinely valuable and PR-worthy — but **the CGP
`hCM` edge is NOT closed**. Reword M4a's theorem name/docstring to
`energy_identity_sequenceModel` (or similar) and state plainly that connecting it to
`energy_identity` requires M4b. Failing to do this reproduces the exact "green theorem
whose stated content isn't what it claims" failure mode the JOURNAL Session-1 audit exists
to prevent.

**[A] (blocking, technical) — M2.2 is under-supported.** Neither of the plan's two routes
works as written: route (a) needs a finite `lintegral`-over-`Measure.pi` Tonelli that is
**not in the pin**, and route (b)'s induction needs `withDensity`-commutes-with-a-measurable-equiv,
also **not in the pin**. Both are surmountable, but the *concrete* missing piece is a small
ForMathlib lemma `map_withDensity_of_measurableEquiv :
(μ.map e).withDensity g = (μ.withDensity (g ∘ e)).map e` (measurable equiv `e`), provable
in ~10–15 lines. **Add it as an explicit M2.2 sub-ticket** rather than discovering it mid-proof.

**[B] (correctness, pervasive) — `Set.Iic` should be `Finset.Iic` throughout.**
`Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n : (ℕ→ℝ) → (↥(Finset.Iic n) → ℝ)` (it is
defined in the `Finset` section of `Order/Restriction.lean` as `(Finset.Iic a).restrict`).
Every `stdGaussian (Set.Iic n)` / `↥(Set.Iic n)` in M2.4/M2.5/M3.1 must read `Finset.Iic n`,
or the types won't line up with `frestrictLe` and `infinitePi_map_restrict`. This is a net
*simplification* (`↥(Finset.Iic n)` has a canonical `Fintype` instance), but it must be
applied consistently.

### Things I could not fully verify (open unknowns for the implementer)

- **`lintegral_prod` orientation / `SigmaFinite` of `withDensity` factors** in M2.2 route
  (b): the factors are probability measures so `SigmaFinite` is fine, but confirm
  `Measure.pi_eq`/`prod_withDensity` accept them without a `[SigmaFinite]` fight.
- **M2.5** `setLIntegral_map` (present) vs the exact `comap`-set unfolding: the membership
  `s ∈ comap (frestrictLe n)` unfolds to `∃ A, MeasurableSet A ∧ frestrictLe n ⁻¹' A = s`;
  confirm the pin's `MeasurableSpace.comap` API gives this cleanly (`measurableSet_comap`).
- **M2.6** whether `Martingale` is easier to obtain via
  `ae_eq_condExp_of_forall_setIntegral_eq` (as planned) or via the pin's
  `martingale_of_condExp` helpers — check both before committing to the longer route.

Everything else in the plan checks out against the pin. The core reduction — sequence
model → 1-D Gaussian densities → prefix filtration → `klDiv_map_tendsto` → Theorem A — is
correct and the hard convergence machinery it leans on is already proved in-repo.

---

## 0. Ground rules (house invariants — violating any of these fails review)

1. **No vacuous edges.** Every hypothesis you introduce must be jointly satisfiable in
   the intended model; every conclusion must be pinned down by the hypotheses (the
   `JOURNAL.md` Session-1 "free variable" test). New theorems here should need **no**
   content edges at all — that is the point of this milestone.
2. **Axiom-clean.** `#print axioms <decl>` = `[propext, Classical.choice, Quot.sound]`
   for every new declaration. Check with a scratch file (see §6), not by eye.
3. **Mathlib style.** `set_option autoImplicit false` (already global); docstrings on
   every public decl stating the math + proof route; naming by Mathlib conventions
   (`klDiv_…`, `absolutelyContinuous_…`, `uniformIntegrable_…`); `theorem` for Props;
   no `sorry` at any commit point; smallest-scope `variable`s; `omit` unused instance
   binders flagged by the linter.
4. **Build protocol.** `export PATH="$HOME/.elan/bin:$PATH"` first (elan not on PATH).
   Iterate with `lake env lean <file>` (~30–60 s; no build lock); full `lake build` only
   at milestone ends and **never concurrently** with another agent. Full-output error
   grep (`grep -B2 -A12 "error"` over the whole log), never `tail`.
5. **Commits.** One commit per milestone, message style as in `git log`
   (`feat(closure): …`), `Co-Authored-By` trailer, and the resource tally: the
   post-commit hook auto-records; at session end run
   `python3 .llm_resource_tally/tool reconcile --label implementation && python3 .llm_resource_tally/tool rollup`.
6. **Vendored code is read-only.** `ForMathlib/MeasureTheory/GaussianEntropy.lean`'s
   vendored section (through `klDiv_stdGaussian_map_add`) must not be edited; new lemmas
   go in new files or that file's clearly-marked ORIGINAL section.

---

## 1. File layout (new + touched)

| File | Status | Contents |
|---|---|---|
| `ForMathlib/MeasureTheory/AbsoluteContinuityMartingale.lean` | extend | M1 (L²⇒UI), M2.6 (automatic martingale), M2.8 (composed AC criterion) |
| `ForMathlib/MeasureTheory/PiWithDensity.lean` | **new** | M2.2 (`Measure.pi` of `withDensity` — standalone Mathlib gap-fill) |
| `ForMathlib/MeasureTheory/GaussianCameronMartin.lean` | **new** | M2.1/2.3/2.4/2.5/2.7, M3 (Theorem A + corollaries). Imports: `Mathlib`, `GaussianEntropy`, `AbsoluteContinuityMartingale`, `PiWithDensity`, `KLDataProcessing` |
| `ChenGeorgiouPavon2021/Basic.lean` | extend | M4a (the CGP-facing corollary discharging deterministic `hCM`) |
| `ForMathlib.lean`, `lakefile.toml` | touch | imports (alphabetical), no new lib targets needed |
| Docs (`ROADMAP_ENERGY_IDENTITY.md`, `JOURNAL.md`, `PROOF_PIPELINE.md` §3 table, `AGENTS.md` §9, `formalization.yaml`, `README.md` inventory) | touch | M5 |

Throughout, abbreviate `stdSeqGaussian : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => gaussianReal 0 1)`
(define it, with an `IsProbabilityMeasure` instance — the pin gives
`instance : IsProbabilityMeasure (infinitePi μ)`).

---

## 2. M1 — Brick 1.5: uniformly L²-bounded ⇒ uniformly integrable (T2, do first)

> ✅ **DONE (Fable, 2026-07-07)** — landed as
> `uniformIntegrable_one_of_lintegral_sq_bdd` in `AbsoluteContinuityMartingale.lean`, with
> the signature below plus `(hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n)` (the nonneg-density setting; it
> lets the tail bound avoid all measurability-of-the-tail-set issues). Proof exactly as
> sketched: pointwise `‖·‖ₑ ≤ ‖·‖ₑ²/C` on the tail set, `C := (M/ofReal ε).toNNReal + 1`.

**Statement (recommended form — lintegral-of-square hypothesis, painless to consume):**

```lean
theorem uniformIntegrable_one_of_lintegral_sq_bdd
    {Ω : Type*} {m : MeasurableSpace Ω} {ν : Measure Ω} [IsFiniteMeasure ν]
    {Z : ℕ → Ω → ℝ} (hmeas : ∀ n, AEStronglyMeasurable (Z n) ν)
    {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hL2 : ∀ n, ∫⁻ x, ENNReal.ofReal (Z n x) ^ 2 ∂ν ≤ M)
    (hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n) :
    UniformIntegrable Z 1 ν
```

(If you prefer the `eLpNorm` phrasing, add a one-line bridge lemma; downstream (M2.7)
produces the lintegral form naturally.)

**Proof sketch.** Apply the pin's
`MeasureTheory.uniformIntegrable_of (hp := le_refl 1) (hp' := one_ne_top)` — it asks: for
every `ε > 0` a `C : ℝ≥0` with
`eLpNorm ({x | C ≤ ‖Z n x‖₊}.indicator (Z n)) 1 ν ≤ ENNReal.ofReal ε` for all `n`.
On the tail set, `C ≤ ‖Z n x‖₊` gives the pointwise bound
`‖Z n x‖ₑ ≤ ‖Z n x‖ₑ ^ 2 / C`, so
`eLpNorm (indicator …) 1 ν = ∫⁻ x in {C ≤ ‖Z n x‖₊}, ‖Z n x‖ₑ ∂ν ≤ C⁻¹ * M`.
Choose `C := (M / ENNReal.ofReal ε).toNNReal + 1` (or any explicit choice making
`C⁻¹ * M ≤ ofReal ε`). No Hölder needed — this is the elementary Chebyshev-style
truncation. Pin support: `eLpNorm_one_eq_lintegral_enorm`,
`lintegral_indicator`, `ENNReal.div_le_iff`-family. (`pow_mul_meas_ge_le_eLpNorm` exists
if you prefer the packaged Chebyshev, but the pointwise route is shorter.)

**Pitfalls.** (i) `‖·‖₊` (`ℝ≥0`) vs `‖·`‖ₑ` (`ℝ≥0∞`) coercion mismatches — normalize to
`‖·‖ₑ` early via `enorm_eq_nnnorm`-style simp lemmas. (ii) For nonneg `Z`,
`‖Z n x‖ₑ = ENNReal.ofReal (Z n x)` needs the a.e. nonnegativity — do the rewrite under
`filter_upwards [hnonneg n]`. (iii) `UniformIntegrable` also packages a uniform
`eLpNorm … 1` bound; get it from `hL2` + Cauchy–Schwarz on a probability space, or
directly `eLpNorm f 1 ≤ eLpNorm f 2 * (measure univ)^(1/2)` (`eLpNorm_le_eLpNorm_of_exponent_le`
on finite measures) — check which the `uniformIntegrable_of` output already supplies
(it derives the bound itself; read its statement first).

**Acceptance.** `lake env lean` clean; axiom-check; the lemma is consumed verbatim by
M2.8.

---

## 3. M2 — Brick 2: the Cameron–Martin density process (the cost centre)

### M2.1 — 1-D shifted-Gaussian `withDensity` representation (T1/T2)

```lean
theorem gaussianReal_shift_eq_withDensity (c : ℝ) :
    gaussianReal c 1 = (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (c * x - 2⁻¹ * c ^ 2)))
```

**Route.** `gaussianReal_of_var_ne_zero` writes both sides as `volume.withDensity` of
their `gaussianPDF`s; `withDensity_mul`-composition (`(μ.withDensity f).withDensity g =
μ.withDensity (f * g)` — grep exact name/argument order) reduces to the pdf algebra
`gaussianPDF 0 1 x * ofReal (exp (c*x − ½c²)) = gaussianPDF c 1 x`, which is exactly the
`hpdf` computation already done inside the vendored `klDiv_gaussianReal_shift` (lines
86–92 of `GaussianEntropy.lean`) — replay it, don't refactor the vendored proof.
Mind `ENNReal.ofReal_mul` (needs a nonneg factor) and `Real.exp_add`.

### M2.2 — `Measure.pi` of `withDensity` (standalone gap-fill; own file `PiWithDensity.lean`)

> ✅ **REVIEW flag [A] — ADDRESSED & IMPLEMENTED (Fable, 2026-07-07).** Route (a) was a dead
> end (no finite `lintegral`-over-`Measure.pi` Tonelli in the pin). The whole milestone is now
> **done, axiom-clean**, in `ForMathlib/MeasureTheory/PiWithDensity.lean`:
> `map_withDensity_measurableEquiv` (the previously-missing sub-lemma: `withDensity` commutes
> with a measurable equiv), `pi_withDensity` (`Fin n` induction via `piFinSuccAbove` +
> `prod_withDensity`, then Fintype transport via `piCongrLeft`, mirroring the vendored
> `klDiv_pi`/`klDiv_pi_fintype`), and the Tonelli corollary `lintegral_pi_prod`
> (`∫⁻ ∏ᵢ fᵢ(xᵢ) ∂Measure.pi μ = ∏ᵢ ∫⁻ fᵢ dμᵢ`) which **defuses M2.7's remaining friction**.
> Opus: consume these; do not re-prove.

```lean
theorem pi_withDensity {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
```

(The `SigmaFinite` instance argument on the density factors is discharged automatically in
the Gaussian application, where each factor is a probability measure.)

### M2.3 — finite-dimensional CM density (T1 given M2.1+M2.2)

```lean
theorem stdGaussian_map_add_eq_withDensity {ι : Type*} [Fintype ι] (h : ι → ℝ) :
    (stdGaussian ι).map (· + h) = (stdGaussian ι).withDensity
      (fun x => ENNReal.ofReal (Real.exp (∑ i, (h i * x i - 2⁻¹ * h i ^ 2))))
```

**Route.** The vendored `hmap` step inside `klDiv_stdGaussian_map_add` proves
`(stdGaussian ι).map (· + h) = Measure.pi (fun i => gaussianReal (h i) 1)` — extract
that computation as a standalone lemma `stdGaussian_map_add` (new, in
`GaussianCameronMartin.lean`; copy the 6-line proof, cite the vendored original in the
docstring). Then M2.1 per coordinate + M2.2 + `Real.exp_sum` / `ENNReal.ofReal` product
bookkeeping (`ENNReal.ofReal_prod_of_nonneg`? grep; else `Finset.prod_induction`).

### M2.4 — prefix marginals of the sequence model (T2, fiddly types)

> ✅ **REVIEW flag [B] — ADDRESSED (statements retyped).** `Preorder.frestrictLe` (the version
> the repo's filtration machinery uses) lives in the **`Finset` section** of
> `Order/Restriction.lean`: `frestrictLe a = (Finset.Iic a).restrict` **definitionally**. All
> statements in this plan now use `Finset.Iic n`; `↥(Finset.Iic n)` has a canonical `Fintype`
> instance, so `stdGaussian (Finset.Iic n)` typechecks directly. With that fix this ticket is
> nearly a direct application of the pin lemma — difficulty downgraded to 1–2.

```lean
theorem stdSeqGaussian_map_frestrictLe (n : ℕ) :
    stdSeqGaussian.map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
      = stdGaussian (Finset.Iic n)
```

**Route.** `Preorder.frestrictLe n = (Finset.Iic n).restrict := rfl`, so this is
`Measure.infinitePi_map_restrict (I := Finset.Iic n)` plus unfolding
`stdGaussian (Finset.Iic n) = Measure.pi (fun _ : Finset.Iic n => gaussianReal 0 1)`
(definitional). Expect ≤ 5 lines. (If the `rfl` between `frestrictLe n` and
`Finset.restrict` needs nudging, `show`-cast the map before applying the pin lemma.)

**Also prove the shift-commutation (one-liner, funext):**
```lean
theorem frestrictLe_add (c : ℕ → ℝ) (n : ℕ) (x : ℕ → ℝ) :
    Preorder.frestrictLe n (x + c)
      = Preorder.frestrictLe n x + Preorder.frestrictLe n c := rfl
```
so `stdSeqGaussian.map (· + c) |>.map (frestrictLe n) = (stdGaussian (Iic n)).map (· + c↾)`
via `Measure.map_map` (measurability sides: `Preorder.measurable_frestrictLe`,
`measurable_add_const`).

### M2.5 — the density process and its local-density property (T2)

```lean
noncomputable def cmDensityProcess (c : ℕ → ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
    Real.exp (∑ i ∈ Finset.Iic n, (c i * x i - 2⁻¹ * c i ^ 2))
```

(Real-valued, strictly positive, `ℱ n`-measurable by construction: it reads only
coordinates `≤ n`. Keeping the sum over `Finset.Iic n` of the *ambient* coordinates —
rather than composing with `frestrictLe` — avoids subtype noise in the martingale steps;
prove a `rfl`/`funext` lemma relating it to `(finite density) ∘ frestrictLe n` where M2.3
is applied.)

```lean
theorem map_add_eq_lintegral_cmDensityProcess (c : ℕ → ℝ) (n : ℕ) {s : Set (ℕ → ℝ)}
    (hs : MeasurableSet[(MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)] s) :
    stdSeqGaussian.map (· + c) s
      = ∫⁻ x in s, ENNReal.ofReal (cmDensityProcess c n x) ∂stdSeqGaussian
```

**Route.** `hs` unfolds (`MeasurableSpace.comap`: membership is
`∃ A, MeasurableSet A ∧ frestrictLe n ⁻¹' A = s`) to `s = (frestrictLe n)⁻¹' A`. Then:
LHS `= (P.map (frestrictLe n)) A` (`Measure.map_apply`) `= ((stdGaussian (Iic n)).map (· + c↾)) A`
(M2.4 + shift-commutation) `= ∫⁻ y in A, ρ y ∂stdGaussian (Iic n)` (M2.3 +
`withDensity_apply`) `= ∫⁻ x in s, ρ (frestrictLe n x) ∂stdSeqGaussian` (M2.4 backwards +
`setLIntegral_map`) `= RHS` (the `rfl`-bridge between `ρ ∘ frestrictLe n` and
`cmDensityProcess c n`; the finite sum over the subtype `i : ↥(Finset.Iic n)` vs
`i ∈ Finset.Iic n` converts by `Finset.sum_coe_sort` — pin down this conversion once
in a private lemma).

### M2.6 — automatic martingale from local densities (general, upstreamable; T2)

> ✅ **DONE (Fable, 2026-07-07)** — landed as `martingale_of_setLIntegral_eq` +
> `absolutelyContinuous_of_localDensity` in `AbsoluteContinuityMartingale.lean`. Note the
> adaptedness hypothesis is **`StronglyAdapted ℱ Z`** (this pin's `Martingale` is
> `StronglyAdapted ∧ tower`; its `Adapted` is `Measurable`-based and is NOT what the
> constructor wants). Otherwise exactly as sketched below.

**The insight (verified in the survey): the martingale property is FREE — it follows
from the consistency of the local-density property across levels, no Gaussian
computation.** Prove it in `AbsoluteContinuityMartingale.lean`, right before the existing
theorem, in the same generality:

```lean
theorem martingale_of_setLIntegral_eq {Ω : Type*} {m : MeasurableSpace Ω}
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m) (Z : ℕ → Ω → ℝ)
    (hadapted : ∀ n, StronglyMeasurable[ℱ n] (Z n))
    (hnonneg : ∀ n, 0 ≤ᵐ[ν] Z n)
    (hdens : ∀ n, ∀ s, MeasurableSet[ℱ n] s
      → μ s = ∫⁻ x in s, ENNReal.ofReal (Z n x) ∂ν) :
    Martingale Z ℱ ν
```

**Route.** Integrability: `hdens n Set.univ` gives `∫⁻ ofReal (Z n) = μ univ = 1`;
with `hnonneg` and measurability this yields `Integrable (Z n) ν`
(`integrable_of_lintegral_ofReal_lt_top`-shaped; the existing file already does this
conversion dance — reuse its idioms `ofReal_integral_eq_lintegral_ofReal`).
Martingale: `martingale_iff`-style, show `ν[Z m | ℱ n] =ᵐ Z n` for `n ≤ m` via
`MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq` (pin-present): for `s ∈ ℱ n`,
`∫ x in s, Z m ∂ν = (μ s).toReal = ∫ x in s, Z n ∂ν` — both from `hdens` (`s ∈ ℱ n ≤ ℱ m`),
converting `∫⁻ ofReal ↔ ∫` under nonneg+integrable as above. Supply the side conditions
(`IntegrableOn` from global integrability; `AEStronglyMeasurable[ℱ n]` from `hadapted`).

**Then refactor-compose (still M2.6):**
```lean
theorem absolutelyContinuous_of_localDensity
    (… same as absolutelyContinuous_of_densityProcess but with hmart REPLACED by
       hadapted, and hUI REPLACED by the M1 lintegral-square bound …) : μ ≪ ν
```
= `absolutelyContinuous_of_densityProcess` ∘ (`martingale_of_setLIntegral_eq`,
`uniformIntegrable_one_of_lintegral_sq_bdd`). Keep the original theorem untouched (it is
the cleaner Mathlib-PR unit); the composed form is the convenience API M2.8 consumes.

### M2.7 — the L² bound (T2)

```lean
theorem lintegral_sq_cmDensityProcess_le (c : ℕ → ℝ) (hc : Summable (fun n => c n ^ 2)) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (cmDensityProcess c n x) ^ 2 ∂stdSeqGaussian
      ≤ ENNReal.ofReal (Real.exp (∑' i, c i ^ 2))
```

**Route.** `(cmDensityProcess c n)² = exp (∑_{i ∈ Iic n} (2cᵢ xᵢ − cᵢ²))` (exp algebra).
Push through M2.4 to a finite-product integral over `stdGaussian (Finset.Iic n)`; factor
the integrand as `∏ i, exp (2cᵢ xᵢ − cᵢ²)` and use the **now-proved**
`ForMathlib.MeasureTheory.lintegral_pi_prod` (M2.2 deliverable) to reduce to 1-D
integrals; each is
`∫ exp (2cᵢ x) dN(0,1) · exp (−cᵢ²) = exp (2cᵢ²) · exp (−cᵢ²) = exp (cᵢ²)` by the pin's
**`mgf_id_gaussianReal`** (`mgf id (gaussianReal 0 1) t = exp (t²/2)` at `t = 2cᵢ`;
`mgf` is by definition `∫ exp (t·x)`, so unfold `ProbabilityTheory.mgf` or use
`mgf_gaussianReal` with `p.map id`). Total: `exp (∑_{Iic n} cᵢ²) ≤ exp (∑' cᵢ²)` by
`Finset.sum_le_tsum` (nonneg terms) + `Real.exp_le_exp`. Mind lintegral↔integral: the
integrand is nonneg and integrable (mgf finiteness — `gaussianReal` has all exponential
moments; pin: `memLp_id_gaussianReal` / integrability from `mgf` machinery —
`ProbabilityTheory.integrable_exp_mul_of_mem_interior`? grep; for the Gaussian the
clean route is `integrable_exp_mul_gaussianReal`-shaped or via `mgf_pos_iff`).

### M2.8 — the Kakutani `≪` instance (T1 given the above)

```lean
theorem absolutelyContinuous_stdSeqGaussian_map_add (c : ℕ → ℝ)
    (hc : Summable (fun n => c n ^ 2)) :
    stdSeqGaussian.map (· + c) ≪ stdSeqGaussian
```

= `absolutelyContinuous_of_localDensity` with `ℱ n := comap (frestrictLe n)` (build the
`Filtration` value exactly as `PathEmbedding.lean` lines 143–155 already does — copy that
`ℱ` construction into a shared `def prefixFiltration` if you touch it twice),
`hgen := iSup_comap_frestrictLe_eq_pi`, `Z := cmDensityProcess c`,
`hdens := M2.5`, adaptedness from the coordinate structure, L² bound from M2.7 via M1.
`IsProbabilityMeasure (stdSeqGaussian.map (· + c))`: `Measure.isProbabilityMeasure_map`.

**Commit M1+M2 together** as `feat(closure): Cameron–Martin density martingale — the
sequence-model ≪ (Kakutani instance)`.

---

## 4. M3 — Theorem A and corollaries (the payoff; T2 given M2)

### M3.1 — grid KL formula

```lean
theorem klDiv_map_frestrictLe_stdSeqGaussian_shift (c : ℕ → ℝ) (n : ℕ) :
    klDiv ((stdSeqGaussian.map (· + c)).map (Preorder.frestrictLe n))
          (stdSeqGaussian.map (Preorder.frestrictLe n))
      = ENNReal.ofReal (2⁻¹ * ∑ i ∈ Finset.Iic n, c i ^ 2)
```
= M2.4 + shift-commutation + vendored `klDiv_stdGaussian_map_add` at `ι := ↥(Finset.Iic n)`
(+ the `Finset.sum_coe_sort` conversion from M2.5).

### M3.2 — tail convergence

`Tendsto (fun n => ofReal (2⁻¹ * ∑ i ∈ Finset.Iic n, c i ^ 2)) atTop (𝓝 (ofReal (2⁻¹ * ∑' i, c i ^ 2)))`:
`Summable.hasSum → HasSum.tendsto_sum_nat` gives `Finset.range`-sums; convert
`Finset.Iic n = Finset.range (n+1)` (`Nat.Iic_eq_range'`-family; grep — worst case
`Finset.ext` + `Nat.lt_succ_iff`, then compose with `tendsto_atTop_atTop`-shifted index
via `Filter.tendsto_add_atTop_iff_nat`); then `ENNReal.continuous_ofReal.tendsto` and
`Continuous.const_mul`.

### M3.3 — **Theorem A**

```lean
/-- **Infinite-dimensional Cameron–Martin / Kakutani KL identity.** Shifting the iid
standard-Gaussian sequence law by an `ℓ²` vector `c` costs relative entropy exactly
`½‖c‖²_{ℓ²}` — the continuum Cameron–Martin energy. … -/
theorem klDiv_stdSeqGaussian_map_add (c : ℕ → ℝ) (hc : Summable (fun n => c n ^ 2)) :
    klDiv (stdSeqGaussian.map (· + c)) stdSeqGaussian
      = ENNReal.ofReal (2⁻¹ * ∑' n, c n ^ 2)
```

**Route.** `klDiv_map_tendsto` (the `hfin`-free `ℝ≥0∞` martingale-convergence identity,
`KLDataProcessing.lean:234`) with `g n := frestrictLe n`, the `prefixFiltration`, `hℱ n := rfl`,
`hgen := iSup_comap_frestrictLe_eq_pi`, and `hac := M2.8` gives grid-KLs `→ klDiv P R`;
M3.1+M3.2 give grid-KLs `→ ofReal (½∑')`; `tendsto_nhds_unique` (ℝ≥0∞ is Hausdorff)
closes it. **Corollaries** (each 1–3 lines): `klDiv_stdSeqGaussian_map_add_ne_top`
(finiteness — from the identity, `ofReal ≠ ⊤`) and the `toReal` form
`toReal_klDiv_stdSeqGaussian_map_add : … = 2⁻¹ * ∑' n, c n ^ 2` (`toReal_ofReal`,
nonneg by `tsum_nonneg`).

**Commit** as `feat(closure): Theorem A — infinite-dimensional Cameron–Martin KL identity`.

---

## 5. M4 — wiring into `ChenGeorgiouPavon2021`

### M4a — the sequence-model energy identity (required; honest scope)

> ✅ **REVIEW flag [C] — ADDRESSED (statement re-scoped).** The previous draft claimed this
> "discharges the `hCM` edge of `energy_identity`" — **false**: Theorem A lives on the abstract
> sequence model `stdSeqGaussian`, not on CGP's SDE path kernels `Kᵘ_x`/`Kᵂ_x`; identifying the
> two is exactly the deferred (stretch) M4b. The deliverable of M1–M4a is therefore: **a
> standalone, Mathlib-quality infinite-dimensional Cameron–Martin/Kakutani KL identity, plus its
> CGP-facing restatement for the sequence *model*** — genuinely valuable and upstream-worthy,
> but the CGP `hCM` edge itself remains an explicit (satisfiable, discrete-instance-proved)
> hypothesis until M4b lands. All docs written in M5 must say this plainly.

Add to `ChenGeorgiouPavon2021/Basic.lean` (after `energy_identity_euler_maruyama`):

```lean
/-- **Deterministic continuum energy identity — sequence model** (CGP (4.19), deterministic
open-loop drift, in canonical iid-Gaussian coordinates). For the canonical model of the
driving noise — the iid standard-Gaussian sequence law — the Cameron–Martin-shifted law by
an `ℓ²` vector `c` has relative entropy exactly the control energy `½‖c‖²_{ℓ²}`. Delegates
to `ForMathlib.MeasureTheory.klDiv_stdSeqGaussian_map_add` (Theorem A).

This is the deterministic Cameron–Martin **content** of the `hCM` edge in canonical
coordinates. It does **NOT** by itself discharge `energy_identity`'s `hCM` hypothesis:
that edge is stated over the SDE path kernels `Kᵘ_x`/`Kᵂ_x`, and identifying those with
the sequence model (Lévy–Ciesielski / nested-dyadic transport of `wienerMeasure`) is the
open M4b step — see `PLAN_CONTINUUM_CLOSURE.md`. The discrete instance of the same
content is `energy_identity_euler_maruyama`; `tendsto_emEnergy_sampled` gives the
quadrature link between the discrete energies and `∫₀¹ ½‖u_t‖² dt`. Feedback drift
remains the honest Itô-blocked edge (PROOF_PIPELINE §2). -/
theorem energy_identity_sequenceModel (c : ℕ → ℝ)
    (hc : Summable (fun n => c n ^ 2)) :
    (klDiv (stdSeqGaussian.map (· + c)) stdSeqGaussian).toReal = 2⁻¹ * ∑' n, c n ^ 2
```

(delegation, one line) **plus** the quadrature link stated as a separate corollary
combining it with `tendsto_emEnergy_sampled` for `c` given by grid-sampled controls —
state it so that *no* new analytic content is needed (the `∑' = lim ∑` side is M3.2's
machinery; do NOT promise `∑' c² = ∫v²` for a fixed `c` unless `c` is literally defined
as the increments, in which case it is `tendsto`-phrased, not an equality — keep the
statement honest and `tendsto`-shaped).

### M4b — path-level (Wiener) transport (STRETCH — finite layer landed; continuum closure remains)

**Current status (2026-07-08):** the finite dyadic part of this stretch is no longer speculative.
The repo now has a green finite-dimensional Wiener/dyadic bridge: raw dyadic increment laws,
normalization/scaling to standard Gaussians, independence/product assembly, finite shifted-grid
with-density formulas, and finite dyadic absolute continuity. The remaining part of M4b is the
continuum closure, not another finite Gaussian calculation.

**Model correction before further proof work:** the old ambient `RealPath := ℝ → ℝ` is too broad
for a full dyadic-generator theorem. Future continuum theorems should move to an anchored interval
path space (eventually continuous paths, e.g. a `C₀([0,1], ℝ)`-style carrier) or explicitly add the
support/anchor assumptions needed to make dyadic observations generating.

The original survey found real pin support: `iIndepFun_of_covariance_eq_zero`
(`Gaussian/IsGaussianProcess/Independence.lean`) + `iIndepFun_iff_map_fun_eq_infinitePi_map`
(`Independence/InfinitePi.lean`). Route: fixed dyadic level `k` — the `2^k` increments of
`BrownianReal.projectiveFamily` are a Gaussian family (pin:
`measurePreserving_eval_sub_eval_projectiveFamily` for each) with zero cross-covariance
(compute from `covariance_eval_projectiveFamily`: `cov(ω_t−ω_s, ω_v−ω_u) = min(t,v) −
min(t,u) − min(s,v) + min(s,u) = 0` for disjoint `(s,t]`, `(u,v]`) — hence **jointly**
independent, hence the level-`k` increment vector's law is the finite product of
`gaussianReal 0 Δ`. This identifies the sampled-Wiener finite marginals with images of
`stdGaussian` and enables a `wienerMeasure`-facing restatement of Theorem A along nested
dyadic filtrations. **Scope it as its own session; write the plan-of-record into the
journal before starting; do not let it block M5.** If the increment-vector covariance
algebra fights you for more than ~2 hours, record the exact blocker in the journal and
stop — M4a already discharges the deterministic `hCM` honestly.

---

## 6. M5 — verification, docs, commits (non-negotiable checklist)

1. **Full build**: `lake build` green; only pre-existing warnings.
2. **Axiom check** (scratchpad file, `lake env lean` it):
   `#print axioms` on — `uniformIntegrable_one_of_lintegral_sq_bdd`,
   `martingale_of_setLIntegral_eq`, `absolutelyContinuous_of_localDensity`,
   `Measure.pi_withDensity`, `gaussianReal_shift_eq_withDensity`,
   `stdGaussian_map_add_eq_withDensity`, `stdSeqGaussian_map_frestrictLe`,
   `map_add_eq_lintegral_cmDensityProcess`, `lintegral_sq_cmDensityProcess_le`,
   `absolutelyContinuous_stdSeqGaussian_map_add`, `klDiv_stdSeqGaussian_map_add`,
   `energy_identity_deterministic_continuum` — all `[propext, Classical.choice, Quot.sound]`.
3. **Docs**: Session-7 documentation update landed by GPT-5.5 Thinking (2026-07-08):
   JOURNAL.md, ROADMAP_ENERGY_IDENTITY.md, PLAN_CONTINUUM_CLOSURE.md, README.md, and
   formalization.yaml mark the sequence-model theorem complete and keep M4b/feedback
   Girsanov separate. Session-8 documentation update additionally records that the finite
   M4b/Wiener dyadic layer is green, while KL exhaustion and CM path-space quasi-invariance
   remain explicit continuum interfaces pending a corrected interval path carrier.
4. **Commits**: milestone-per-commit (M1+M2, M3, M4, M5-docs), tally reconcile+rollup at
   session end, then bump the submodule pointer in the parent repo (only this submodule).

## 7. Risk register (ranked)

| Risk | Ticket | Mitigation |
|---|---|---|
| `Set.Iic`/`Finset.Iic` subtype plumbing costs more than the math | M2.4/M2.5 | `rfl`-test defeq first; centralize the conversion in one private lemma; mirror `klDiv_pi_fintype` |
| finite-pi Tonelli/`withDensity` product lemmas missing from pin | M2.2/M2.7 | fallback induction route spelled out in M2.2(b); the 2-factor `lintegral_prod` IS in the pin |
| `ae_eq_condExp_of_forall_setIntegral_eq` side conditions (trim/σ-finite) | M2.6 | probability measures throughout; copy hypothesis-shape from `Martingale.ae_eq_condExp_limitProcess`'s call sites |
| lintegral↔Bochner conversions proliferate | M2.5–M2.7 | standardize on `ofReal_integral_eq_lintegral_ofReal` (already used in `AbsoluteContinuityMartingale.lean`) |
| M4b covariance algebra (nested grids, `ℝ≥0` subtraction) | M4b | stretch-scoped; hard stop + journal note after ~2h of fighting `NNReal` arithmetic |
| scope creep toward the feedback case | — | forbidden by plan; it is Itô-blocked (survey §3) — any "clever" route around the stochastic integral is a red flag for a vacuous edge |
