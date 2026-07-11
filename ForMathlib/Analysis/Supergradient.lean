/-
# Supergradients of concave functions on `ℝ`, and the DRO optimal multiplier

This file develops the one-dimensional supergradient existence theorem from Mathlib's
`ConcaveOn`, `ConvexOn`, and slope-monotonicity lemmas.

## Why

The `≥` half of Wasserstein-DRO strong duality (`GaoKleywegt2023.strong_duality_thm1`'s `hge`,
Blanchet–Murthy Thm 1) has two ingredients:

1. the Lagrangian value is *achieved* by a pushforward along a measurable near-maximizer of the
   `c`-transform — `ForMathlib.OT.exists_coupling_lagrangian_ge`, proved;
2. **an optimal multiplier `λ* ≥ 0` with complementary slackness**, so that the Lagrangian relaxation
   at `λ*` is bounded by the constrained value. That is exactly `exists_nonneg_multiplier` below,
   applied to the DRO value function `h t = sup { 𝔼_μ[f] : 𝔼_π[c] ≤ t }`.

`h` is concave (mix two couplings) and nondecreasing (relax the budget), so it has a nonnegative
supergradient `λ*` at an interior radius `δ`, and

`h t + λ*·(δ − t) ≤ h δ`  for every `t`,

which is precisely "the Lagrangian relaxation at `λ*` does not exceed the constrained optimum".

## The geometry, in one line

For a concave `h`, the slopes `(h t − h δ)/(t − δ)` decrease as `t` increases past `δ`. So the
supremum of the *right-hand* slopes is dominated by every *left-hand* slope, and that supremum is a
supergradient.
-/
import Mathlib

set_option autoImplicit false

open Set

namespace ForMathlib.Analysis

/-- **Supergradient existence for a concave function on an interval of `ℝ`.** At an interior point
`δ` there is an `m` with `h t ≤ h δ + m · (t − δ)` for all `t` in the interval.

`m` is the supremum of the right-hand slopes at `δ`; concavity (`ConcaveOn.slope_anti_adjacent`)
makes every left-hand slope an upper bound for that set, which is what handles `t < δ`. -/
theorem exists_supergradient_of_concaveOn {a b : ℝ} {h : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc a b) h) {δ : ℝ} (hδ : δ ∈ Ioo a b) :
    ∃ m : ℝ, ∀ t ∈ Icc a b, h t ≤ h δ + m * (t - δ) := by
  obtain ⟨haδ, hδb⟩ := hδ
  have hmemδ : δ ∈ Icc a b := ⟨haδ.le, hδb.le⟩
  have hmema : a ∈ Icc a b := ⟨le_refl a, (haδ.trans hδb).le⟩
  have hmemb : b ∈ Icc a b := ⟨(haδ.trans hδb).le, le_refl b⟩
  -- the set of right-hand slopes at `δ`
  set S : Set ℝ := (fun t => (h t - h δ) / (t - δ)) '' Ioc δ b with hSdef
  have hSne : S.Nonempty := ⟨_, ⟨b, ⟨hδb, le_refl b⟩, rfl⟩⟩
  -- every right slope is at most the left slope from `a`
  have hub : ∀ s ∈ S, s ≤ (h δ - h a) / (δ - a) := by
    rintro s ⟨t, ⟨hδt, htb⟩, rfl⟩
    exact hconc.slope_anti_adjacent hmema ⟨(haδ.trans hδt).le, htb⟩ haδ hδt
  have hSbdd : BddAbove S := ⟨_, hub⟩
  refine ⟨sSup S, fun t ht => ?_⟩
  rcases lt_trichotomy t δ with hlt | heq | hgt
  · -- `t < δ`: the slope from `t` to `δ` dominates every right slope
    have hkey : sSup S ≤ (h δ - h t) / (δ - t) := by
      refine csSup_le hSne ?_
      rintro s ⟨u, ⟨hδu, hub'⟩, rfl⟩
      exact hconc.slope_anti_adjacent ht ⟨ht.1.trans (hlt.trans hδu).le, hub'⟩ hlt hδu
    have hpos : 0 < δ - t := by linarith
    rw [le_div_iff₀ hpos] at hkey
    have hring : sSup S * (t - δ) = -(sSup S * (δ - t)) := by ring
    linarith [hring]
  · subst heq; simp
  · -- `δ < t`: the slope from `δ` to `t` is in `S`
    have hmem : (h t - h δ) / (t - δ) ∈ S := ⟨t, ⟨hgt, ht.2⟩, rfl⟩
    have hle : (h t - h δ) / (t - δ) ≤ sSup S := le_csSup hSbdd hmem
    have hpos : 0 < t - δ := by linarith
    rw [div_le_iff₀ hpos] at hle
    linarith


/-- The supergradient of a **nondecreasing** concave function is nonnegative. -/
theorem exists_nonneg_supergradient_of_concaveOn {a b : ℝ} {h : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc a b) h) (hmono : MonotoneOn h (Icc a b)) {δ : ℝ} (hδ : δ ∈ Ioo a b) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ t ∈ Icc a b, h t ≤ h δ + m * (t - δ) := by
  obtain ⟨haδ, hδb⟩ := hδ
  obtain ⟨m, hm⟩ := exists_supergradient_of_concaveOn hconc ⟨haδ, hδb⟩
  refine ⟨m, ?_, hm⟩
  -- test the supergradient inequality at `b > δ`
  have hmemδ : δ ∈ Icc a b := ⟨haδ.le, hδb.le⟩
  have hmemb : b ∈ Icc a b := ⟨(haδ.trans hδb).le, le_refl b⟩
  have h1 : h δ ≤ h b := hmono hmemδ hmemb hδb.le
  have h2 : h b ≤ h δ + m * (b - δ) := hm b hmemb
  have hpos : 0 < b - δ := by linarith
  nlinarith [h1, h2]

/-- **The DRO optimal multiplier.** For a nondecreasing concave value function `h` and an interior
radius `δ`, there is a multiplier `λ* ≥ 0` whose Lagrangian relaxation never exceeds the constrained
optimum:

`h t + λ* · (δ − t) ≤ h δ`  for every `t` in the interval.

This is ingredient (2) of `hge`; ingredient (1) is `ForMathlib.OT.exists_coupling_lagrangian_ge`.
Taking the supremum over `t` on the left gives `inf_λ (λδ + 𝔼_ν[φ_λ]) ≤ h δ = primalValue`, which is
`hge` itself — once the DRO value function is known to be concave and nondecreasing. -/
theorem exists_nonneg_multiplier {a b : ℝ} {h : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc a b) h) (hmono : MonotoneOn h (Icc a b)) {δ : ℝ} (hδ : δ ∈ Ioo a b) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ t ∈ Icc a b, h t + m * (δ - t) ≤ h δ := by
  obtain ⟨m, hm0, hm⟩ := exists_nonneg_supergradient_of_concaveOn hconc hmono hδ
  refine ⟨m, hm0, fun t ht => ?_⟩
  have := hm t ht
  have hring : m * (t - δ) = -(m * (δ - t)) := by ring
  linarith

/-! ## The same, on an arbitrary convex set

The DRO value function lives on `Set.Ici t₀`, not on a compact interval, so the supergradient
statement is repeated for a general convex `s` containing a point on each side of `δ`. The proof is
identical: the supremum of the right-hand slopes is a supergradient, and every left-hand slope
bounds that supremum. -/

/-- **Supergradient existence on a convex subset of `ℝ`.** -/
theorem exists_supergradient_of_concaveOn' {s : Set ℝ} {h : ℝ → ℝ} (hconc : ConcaveOn ℝ s h)
    {a b δ : ℝ} (hamem : a ∈ s) (hbmem : b ∈ s) (haδ : a < δ) (hδb : δ < b) (hδ : δ ∈ s) :
    ∃ m : ℝ, ∀ t ∈ s, h t ≤ h δ + m * (t - δ) := by
  set S : Set ℝ := (fun t => (h t - h δ) / (t - δ)) '' {t | t ∈ s ∧ δ < t} with hSdef
  have hSne : S.Nonempty := ⟨_, ⟨b, ⟨hbmem, hδb⟩, rfl⟩⟩
  have hub : ∀ r ∈ S, r ≤ (h δ - h a) / (δ - a) := by
    rintro r ⟨t, ⟨htmem, hδt⟩, rfl⟩
    exact hconc.slope_anti_adjacent hamem htmem haδ hδt
  have hSbdd : BddAbove S := ⟨_, hub⟩
  refine ⟨sSup S, fun t ht => ?_⟩
  rcases lt_trichotomy t δ with hlt | heq | hgt
  · have hkey : sSup S ≤ (h δ - h t) / (δ - t) := by
      refine csSup_le hSne ?_
      rintro r ⟨u, ⟨humem, hδu⟩, rfl⟩
      exact hconc.slope_anti_adjacent ht humem hlt hδu
    have hpos : 0 < δ - t := by linarith
    rw [le_div_iff₀ hpos] at hkey
    have hring : sSup S * (t - δ) = -(sSup S * (δ - t)) := by ring
    linarith [hring]
  · subst heq; simp
  · have hmem : (h t - h δ) / (t - δ) ∈ S := ⟨t, ⟨ht, hgt⟩, rfl⟩
    have hle : (h t - h δ) / (t - δ) ≤ sSup S := le_csSup hSbdd hmem
    have hpos : 0 < t - δ := by linarith
    rw [div_le_iff₀ hpos] at hle
    linarith

/-- **The DRO optimal multiplier, on a convex set.** For a nondecreasing concave `h` on `s` and
`δ ∈ s` with points of `s` on either side, there is `λ* ≥ 0` with
`h t + λ*·(δ − t) ≤ h δ` for every `t ∈ s`. -/
theorem exists_nonneg_multiplier' {s : Set ℝ} {h : ℝ → ℝ} (hconc : ConcaveOn ℝ s h)
    (hmono : MonotoneOn h s) {a b δ : ℝ} (hamem : a ∈ s) (hbmem : b ∈ s)
    (haδ : a < δ) (hδb : δ < b) (hδ : δ ∈ s) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ t ∈ s, h t + m * (δ - t) ≤ h δ := by
  obtain ⟨m, hm⟩ := exists_supergradient_of_concaveOn' hconc hamem hbmem haδ hδb hδ
  have hm0 : 0 ≤ m := by
    have h1 : h δ ≤ h b := hmono hδ hbmem hδb.le
    have h2 : h b ≤ h δ + m * (b - δ) := hm b hbmem
    have hpos : 0 < b - δ := by linarith
    nlinarith [h1, h2]
  refine ⟨m, hm0, fun t ht => ?_⟩
  have := hm t ht
  have hring : m * (t - δ) = -(m * (δ - t)) := by ring
  linarith

end ForMathlib.Analysis
