# Session journal — ChenGeorgiouPavon2021 soundness audit + fix (2026-07)

Running log of the proof-pass session that audited the last `ChenGeorgiouPavon2021` sorries
for the "hidden `if False then True`" failure mode (a green-but-unsound theorem) and fixed it.
Companion to `AGENTS.md §9`, `PROOF_PIPELINE.md §2`, `formalization.yaml`.

## Starting state (inherited from the fork)
- 5 sorries, all in `ChenGeorgiouPavon2021/Basic.lean`: `energy_identity` (168),
  `optimal_control_eq_grad_log` (292), `optimal_control_eq_sigma_grad_log` (305),
  `optimal_control_eq_grad_value` (356), `optimal_coupling_factorization` (496).
- The fork proved a direction of `dynamic_eq_static_SB` via a new, genuinely-sound
  `ForMathlib.MeasureTheory.toReal_klDiv_map_le` (KL data-processing inequality; verified
  its proof — real conditional-Jensen on the convex KL generator, no hidden falsity).

## Audit finding (the landmine)
Four of the five sorries are **false as stated**, not merely hard:
- `optimal_control_eq_grad_log/_sigma_grad_log/_grad_value` conclude `u* = grad(log φ)` /
  `σ²·grad(log φ)` / `grad(lam)` where **`grad`/`lam` are free operator arguments with no
  hypothesis constraining them to be the actual gradient**. Instantiate `grad := fun _ _ => 0`:
  the hypotheses (`SchrodingerSystem`, `HamiltonJacobi`, `IsOptimalSOC`) remain satisfiable but
  the conclusion `u* = 0` is false. So these can NEVER be discharged soundly as written.
- `optimal_coupling_factorization` concludes `dens_star(x,y) = φhat0 x · p x y · φ1 y` with
  **all of `dens_star,p,φhat0,φ1` free** — false (`dens_star:=0, p:=1,…`), and the conclusion
  is even mis-typed (a pointwise-everywhere density identity where only a.e. can hold).
- **`optimal_control_eq_neg_grad_value` is GREEN but FALSE** — it compiles only because its
  proof `rw`s through the false `optimal_control_eq_grad_log`. This is exactly the hidden
  `if False then True`: it *looks* proved.
- `energy_identity` is the one HONEST sorry — a true Girsanov identity, blocked only by the
  absence of Mathlib path-measure theory. Leave it, clearly labelled.

Blast radius: contained. `Drsb` (the card capstones) references `neg_grad_value` only in a
docstring; it takes `V` abstract, so no card claim depends on the false theorems. Verified by
grep: `grad_log` feeds only `neg_grad_value`; nothing else consumes any of the four.

## Fix strategy (the repo's own "isolate content to an explicit edge" pattern)
Turn each false statement into a TRUE one by isolating the genuine SDE/verification content to
explicit, non-vacuous hypotheses and DERIVING the stated identity — the same posture as every
strong-duality `le_antisymm(weak, attainment-edge)` here.
- Control theorems: add `hHC` (the Hopf–Cole / value-gradient candidate is itself optimal — the
  CGP verification theorem, the real SDE content) + `huniq` (the SOC optimizer is unique — strict
  convexity of the control energy). Then `u* = candidate` is `huniq u* candidate hopt hHC`.
  With `grad:=0`, `hHC` now forces the zero control optimal ⇒ `u*=0` ⇒ conclusion true: no
  counterexample survives. Thread the two edges through `neg_grad_value`.
- Factorization: reformulate to the measure-level Schrödinger factorization — `π_star` equals the
  product-form coupling `π_prod` (density `φ̂(x)·φ(y)` w.r.t. the reference endpoint law), via the
  verification edge (`π_prod` feasible+optimal) + uniqueness of the KL projection. Conclusion is a
  measure/`withDensity` identity (well-typed), not a pointwise density.

## Progress — DONE (2026-07)
- ✅ `optimal_control_eq_grad_log` / `_sigma_grad_log` / `_grad_value`: reformulated with the
  `hHC` (Hopf–Cole / value-gradient candidate optimal) + `huniq` (optimizer unique) edges;
  identity derived by `huniq u* candidate hopt hHC`. Now **axiom-clean** (no `sorryAx`).
- ✅ `optimal_control_eq_neg_grad_value` (was **green but false**): threaded the two edges through
  its call to `grad_log`. Now genuinely **axiom-clean** — the landmine is defused.
- ✅ `optimal_coupling_factorization`: reformulated to the well-typed **measure** identity
  `π* = R₀₁.withDensity(φ̂(x)·φ(y))` via verification (`hprodfeas`/`hprodopt`) + uniqueness
  (`huniq`); derived `π*=π_prod` then rewrote. Now **axiom-clean**.
- ⏳ `energy_identity` (168): intentionally the SOLE remaining sorry — a *true* Girsanov identity
  (`#print axioms` shows the expected `sorryAx`), blocked only by the absence of Mathlib
  continuous path-measure / Girsanov theory. Its discrete Euler–Maruyama layer is already proved
  (`energy_identity_euler_maruyama`, via the vendored Cameron–Martin identity). Closing it means
  building path-measure theory (a multi-month upstream program), not a session.

## Verification
- `#print axioms` on all five reformulated declarations: `[propext, Classical.choice, Quot.sound]`
  (NO `sorryAx`). `energy_identity`: `[propext, sorryAx, Classical.choice, Quot.sound]` (as it
  should be — the one honest sorry). Full `lake build` green (8597 jobs). Sorry count 5 → 1.
- Each reformulation is a TRUE implication with **non-vacuous** premises (all jointly satisfiable
  in the real CGP problem: pick the actual `φ`/potentials, the actual unique optimizer, and the
  true verification facts). No free-operator counterexample survives, and no premise is
  contradictory. The genuine SDE/convexity content is isolated to explicit edges — the same
  posture every strong-duality equality in this repo uses (`le_antisymm(weak, attainment-edge)`).

## Takeaway for the next agent
The "hidden `if False then True`" risk the user flagged was REAL and present (a green theorem
whose stated content was false). The tell: a conclusion that equates a real object to an
**arbitrary free operator/function argument** with no hypothesis linking them. When removing the
last sorries, always ask "is the conclusion actually pinned down by the hypotheses, or could I
instantiate a free variable to break it?" — and confirm with `#print axioms` that a green
downstream theorem doesn't secretly carry `sorryAx` from a false lemma.
