/-
# Measurable ε-argmax selectors (Mathlib-staging)

A **measurable selection of near-maximizers**. Given a family `F i y` measurable in `y` for each
index `i`, and `ε > 0`, we produce a *measurable* `g : Y → ι` with

`F (g y) y > (⨆ i, F i y) − ε`   for every `y`.

## Why this exists

The `≥` half of Wasserstein-DRO strong duality (`GaoKleywegt2023.strong_duality_thm1`'s `hge`,
Blanchet–Murthy Thm 1) is proved by picking a near-optimal multiplier `λ*`, selecting for each
nominal point `y` a near-maximizer `x(y)` of the `c`-transform `sup_x (f x − λ* c(x,y))`, and
pushing the nominal forward along `x(·)`. The push-forward only exists if `x(·)` is **measurable**.

In full generality that step is **Kuratowski–Ryll-Nardzewski measurable selection**, which Mathlib
does not have. But KRN is not needed when the maximization runs over a *countable* index set: an
enumeration plus `Nat.find` gives the selector outright, and the resulting map is measurable because
each "index `k` is the first to beat `S y − ε`" set is a finite Boolean combination of the
measurable sets `{y | S y − ε < F (e j) y}`.

That covers the case the DRSB theory actually needs, via
`exists_measurable_eps_argmax_of_separable`: on a separable domain with an integrand continuous in
`x`, the supremum over `X` equals the supremum over a countable dense subset, so the countable
selector *is* a selector over `X`.

## A junk-value caveat, deliberately surfaced

`⨆ i, F i y` is `Real`'s conditional supremum: on an unbounded family it returns the junk value `0`.
`exists_measurable_eps_argmax` is true regardless — `exists_lt_of_lt_csSup` needs only nonemptiness —
but its conclusion is *informative* only when the family is bounded above. Callers should carry a
`BddAbove` hypothesis for their own reasons; it is not needed here, and asking for it would hide the
fact that the statement is junk-tolerant. Compare the `couplingCost`/`klReal` traps in
`ForMathlib.OT`.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory TopologicalSpace

namespace ForMathlib.MeasureTheory

variable {Y : Type*} [MeasurableSpace Y]

section CountableIndex

variable {ι : Type*} [Countable ι] [Nonempty ι] [MeasurableSpace ι]

omit [Nonempty ι] [MeasurableSpace ι] in
/-- The pointwise supremum of a countable family of measurable functions is measurable. -/
theorem measurable_iSup_of_measurable (F : ι → Y → ℝ) (hF : ∀ i, Measurable (F i)) :
    Measurable fun y => ⨆ i, F i y :=
  Measurable.iSup hF

open Classical in
/-- **Measurable ε-argmax over a countable index set.** For every `ε > 0` there is a measurable
`g : Y → ι` selecting, at each `y`, an index whose value beats `(⨆ i, F i y) − ε`.

The selector is `g y = e (Nat.find _)` for an enumeration `e : ℕ → ι`: the *first* index that beats
the threshold. Measurability is then a finite Boolean combination of measurable sets, via
`Nat.find_eq_iff`.

No `BddAbove` hypothesis: `exists_lt_of_lt_csSup` needs only that the range is nonempty. See the
module docstring on what that means when the family is unbounded. -/
theorem exists_measurable_eps_argmax
    (F : ι → Y → ℝ) (hF : ∀ i, Measurable (F i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Y → ι, Measurable g ∧ ∀ y, (⨆ i, F i y) - ε < F (g y) y := by
  obtain ⟨e, he⟩ : ∃ e : ℕ → ι, Function.Surjective e := exists_surjective_nat ι
  set S : Y → ℝ := fun y => ⨆ i, F i y with hSdef
  have hS : Measurable S := Measurable.iSup hF
  have hex : ∀ y, ∃ n : ℕ, S y - ε < F (e n) y := by
    intro y
    have hlt : S y - ε < S y := by linarith
    obtain ⟨r, ⟨i, rfl⟩, hr⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty _) (by rwa [hSdef] at hlt)
    obtain ⟨n, rfl⟩ := he i
    exact ⟨n, hr⟩
  refine ⟨fun y => e (Nat.find (hex y)), ?_, fun y => Nat.find_spec (hex y)⟩
  have hmeasSet : ∀ j : ℕ, MeasurableSet {y | S y - ε < F (e j) y} := fun j =>
    measurableSet_lt (hS.sub measurable_const) (hF (e j))
  have hn : Measurable fun y => Nat.find (hex y) := by
    refine measurable_to_countable' fun k => ?_
    have hset : (fun y => Nat.find (hex y)) ⁻¹' {k}
        = {y | S y - ε < F (e k) y} ∩ ⋂ j ∈ Finset.range k, {y | ¬ (S y - ε < F (e j) y)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq, Finset.mem_range]
      rw [Nat.find_eq_iff]
    rw [hset]
    exact (hmeasSet k).inter (MeasurableSet.biInter (Set.to_countable _)
      fun j _ => (hmeasSet j).compl)
  exact (measurable_from_top : Measurable e).comp hn

end CountableIndex

/-! ## From a countable index set to a separable domain

The supremum of a continuous function over a separable space is already achieved, up to `ε`, on a
countable dense subset. So the countable selector above *is* a selector over the whole domain. This
is the form the `c`-transform needs: `x ↦ f x − λ c(x, y)` is continuous in `x`, and the DRSB
sample space is separable. -/

section Separable

variable {X : Type*} [TopologicalSpace X] [Nonempty X]

/-- **A continuous function's supremum is unchanged on a dense subset.** -/
theorem sSup_image_dense_eq (D : Set X) (hD : Dense D) (φ : X → ℝ) (hφ : Continuous φ)
    (hbdd : BddAbove (Set.range φ)) :
    sSup (φ '' D) = sSup (Set.range φ) := by
  have hDne : D.Nonempty := hD.nonempty
  have hImNe : (φ '' D).Nonempty := hDne.image φ
  have hImBdd : BddAbove (φ '' D) := hbdd.mono (Set.image_subset_range _ _)
  refine le_antisymm (csSup_le_csSup hbdd hImNe (Set.image_subset_range _ _)) ?_
  refine csSup_le (Set.range_nonempty _) ?_
  rintro r ⟨x, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hopen : IsOpen (φ ⁻¹' Set.Ioi (φ x - ε)) := hφ.isOpen_preimage _ isOpen_Ioi
  have hxmem : x ∈ φ ⁻¹' Set.Ioi (φ x - ε) := by simp; linarith
  obtain ⟨d, hdD, hdU⟩ := hD.exists_mem_open hopen ⟨x, hxmem⟩
  have h1 : φ x - ε < φ d := hdU
  have h2 : φ d ≤ sSup (φ '' D) := le_csSup hImBdd ⟨d, hdD, rfl⟩
  linarith

variable [SeparableSpace X] [MeasurableSpace X]

/-- **Measurable ε-argmax over a separable domain** — the substitute for Kuratowski–Ryll-Nardzewski
that the DRO duality proof actually needs.

`F` is measurable in the parameter `y` and continuous in the maximization variable `x`, and its
supremum in `x` is finite. Then there is a **measurable** `g : Y → X` with
`F (g y) y > (⨆ x, F x y) − ε`.

Proof: take a countable dense `D`, run `exists_measurable_eps_argmax` over the subtype `D`, and note
by `sSup_image_dense_eq` that the supremum over `D` is the supremum over `X`. The `BddAbove`
hypothesis is genuinely used here — unlike in the countable case — because the two suprema agree only
when they are honest suprema. -/
theorem exists_measurable_eps_argmax_of_separable
    (F : X → Y → ℝ) (hFy : ∀ x, Measurable (F x))
    (hFx : ∀ y, Continuous fun x => F x y)
    (hbdd : ∀ y, BddAbove (Set.range fun x => F x y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Y → X, Measurable g ∧ ∀ y, (⨆ x, F x y) - ε < F (g y) y := by
  obtain ⟨D, hDcount, hDdense⟩ := exists_countable_dense X
  haveI : Countable D := hDcount.to_subtype
  haveI : Nonempty D := hDdense.nonempty.to_subtype
  obtain ⟨g', hg'meas, hg'⟩ :=
    exists_measurable_eps_argmax (ι := D) (fun d y => F (d : X) y) (fun d => hFy d) hε
  refine ⟨fun y => (g' y : X), measurable_subtype_coe.comp hg'meas, fun y => ?_⟩
  -- the subtype supremum is the supremum over `D`, which is the supremum over `X`
  have hiSup : (⨆ d : D, F (d : X) y) = ⨆ x, F x y := by
    have h1 : (⨆ d : D, F (d : X) y) = sSup ((fun x => F x y) '' D) := by
      rw [iSup, Set.image_eq_range]
    rw [h1, sSup_image_dense_eq D hDdense (fun x => F x y) (hFx y) (hbdd y)]
    rfl
  rw [← hiSup]
  exact hg' y

end Separable

end ForMathlib.MeasureTheory
