/-
# Measurable embedding of a standard-Borel space into `ℕ → ℝ` (Mathlib-staging)

A standard-Borel space `E` equipped with a **countable point-separating family of measurable
real coordinates** `φ : ℕ → E → ℝ` embeds measurably into the countable product `ℕ → ℝ`, and the
embedding has a **measurable left inverse**. This is the "lossless reparametrisation by countably
many reals" used by `ChenGeorgiouPavon2021.energy_eq_klReal_via_embedding`: a measurable
embedding `e : Path X ↪ (ℕ → ℝ)` with a measurable left inverse.

Two results:

* `exists_measurableEmbedding_nat_of_separating` — the **engine**. For a nonempty standard-Borel
  `E` and a countable measurable family `φ` that jointly separates points, the coordinate map
  `e x = (n ↦ φ n x)` is a measurable embedding (Lusin–Souslin, `Measurable.measurableEmbedding`),
  and `MeasurableEmbedding.invFun` is a measurable left inverse. No topology — pure measurable-space
  content, directly upstreamable.

* `exists_measurableEmbedding_nat_continuousMap` — the **continuous-path instance**. For a compact,
  second-countable, metrizable, nonempty domain `T`, the continuous-function space `C(T, ℝ)`
  (equipped with the Borel σ-algebra of its sup-norm topology; `T` also locally compact) is standard
  Borel, and evaluation at a countable dense set of times `denseSeq T` is a point-separating
  (`Continuous.ext_on`) measurable
  (`continuous_eval_const`) family. So `C(T, ℝ)` embeds measurably into `ℕ → ℝ` with a measurable
  left inverse — the concrete `e`/`g` for the DRSB continuous-path model (`Path X := C([0,1], X)`).

The `C(T, ℝ)` case takes `[MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]` as instances (Mathlib does
not register a measurable space on `C(X, Y)`; `RemyDegenne/brownian-motion` supplies the same
`borel _` instance locally — cited as related work, `DRSB-INDEP`). Requiring the Borel structure as a
hypothesis identifies the intended Borel σ-algebra without adding an orphan
instance on downstream code.
-/
import Mathlib
import ForMathlib.MeasureTheory.KLDataProcessing

open MeasureTheory InformationTheory Topology Set Filter
open scoped ENNReal

namespace ForMathlib.MeasureTheory

/-- **Engine: a countable point-separating measurable family gives a measurable embedding into
`ℕ → ℝ` with a measurable left inverse.**

For a nonempty standard-Borel space `E` and measurable coordinates `φ : ℕ → E → ℝ` that jointly
separate points (`x ↦ (n ↦ φ n x)` is injective), the coordinate map `e x := (n ↦ φ n x)` is a
measurable embedding by Lusin–Souslin (`Measurable.measurableEmbedding`: measurable + injective from
a standard-Borel space into a countably-separated space — `ℕ → ℝ` is standard Borel), so
`MeasurableEmbedding.invFun` is a measurable left inverse.

This is the reusable core discharging the "embedding edge" of the continuum energy identity: a path
law that is determined by countably many measurable readouts is losslessly reparametrised by
`ℕ → ℝ`, so `toReal_klDiv_map_eq_of_leftInverse` transports its KL to the countable-product setting
where the finite-prefix filtration generates the σ-algebra. -/
theorem exists_measurableEmbedding_nat_of_separating
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (φ : ℕ → E → ℝ) (hφ : ∀ n, Measurable (φ n))
    (hsep : Function.Injective (fun x => (fun n => φ n x : ℕ → ℝ))) :
    ∃ (e : E → (ℕ → ℝ)) (g : (ℕ → ℝ) → E),
      Measurable e ∧ Measurable g ∧ Function.LeftInverse g e := by
  set e : E → (ℕ → ℝ) := fun x n => φ n x with he_def
  have he : Measurable e := measurable_pi_lambda e (fun n => hφ n)
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hsep
  exact ⟨e, hemb.invFun, he, hemb.measurable_invFun, hemb.leftInverse_invFun⟩

/-- **Continuous-path instance: `C(T, ℝ)` embeds measurably into `ℕ → ℝ` with a measurable left
inverse**, for `T` compact, second-countable, metrizable, nonempty.

Under these hypotheses `C(T, ℝ)` (sup-norm topology, `ContinuousMap.instMetricSpace`) is a separable
(`ContinuousMap.instSeparableSpace`) complete (`ContinuousMap.instCompleteSpaceOfCompactlyCoherentSpace`)
metric space, hence Polish, hence — with the assumed Borel σ-algebra — standard Borel. Evaluation at
the countable dense time set `denseSeq T` is:
* **measurable** — each `f ↦ f (denseSeq T n)` is continuous (`continuous_eval_const`), so measurable
  for the Borel σ-algebra;
* **point-separating** — two continuous functions agreeing on the dense range `denseSeq T` are equal
  (`Continuous.ext_on` + `DFunLike.coe_injective`).

So the engine `exists_measurableEmbedding_nat_of_separating` applies with
`φ n := fun f => f (denseSeq T n)`. This is the concrete `e`, `g` (with `Measurable`/`LeftInverse`
witnesses) that instantiate the abstract embedding edge of `energy_eq_klReal_via_embedding` for the
standard DRSB continuous-path model `Path X := C([0,1], X)`. -/
theorem exists_measurableEmbedding_nat_continuousMap
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [Nonempty T]
    [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)] :
    ∃ (e : C(T, ℝ) → (ℕ → ℝ)) (g : (ℕ → ℝ) → C(T, ℝ)),
      Measurable e ∧ Measurable g ∧ Function.LeftInverse g e := by
  -- `C(T, ℝ)` is Polish (separable + complete metric), hence standard Borel with its Borel σ-algebra.
  haveI : StandardBorelSpace C(T, ℝ) := inferInstance
  -- evaluation at the `n`-th dense time is measurable (it is continuous)
  have hφ : ∀ n, Measurable (fun f : C(T, ℝ) => f (TopologicalSpace.denseSeq T n)) :=
    fun n => (continuous_eval_const (TopologicalSpace.denseSeq T n)).measurable
  -- dense-time evaluations separate continuous functions
  have hsep : Function.Injective
      (fun (f : C(T, ℝ)) => (fun n => f (TopologicalSpace.denseSeq T n) : ℕ → ℝ)) := by
    intro f f' hff
    apply DFunLike.coe_injective
    refine Continuous.ext_on (TopologicalSpace.denseRange_denseSeq T) f.continuous f'.continuous ?_
    rintro x ⟨n, rfl⟩
    exact congrFun hff n
  exact exists_measurableEmbedding_nat_of_separating
    (fun n f => f (TopologicalSpace.denseSeq T n)) hφ hsep

/-- **The grid-projected divergences through a countable separating family converge to the full KL.**
For probability measures `P ≪ R` with finite `KL(P‖R)` on a nonempty standard-Borel space `E`, and a
countable measurable point-separating family `φ : ℕ → E → ℝ`, the coordinate map `x ↦ (n ↦ φ n x)` is
a KL-preserving measurable embedding into `ℕ → ℝ` (`exists_measurableEmbedding_nat_of_separating` +
`toReal_klDiv_map_eq_of_leftInverse`). Pushing the two measures into `ℕ → ℝ` and projecting onto the
first `n+1` coordinates (`Preorder.frestrictLe n`), the martingale-convergence identity
`klDiv_map_tendsto_toReal` — whose generation hypothesis is supplied by
`iSup_comap_frestrictLe_eq_pi` on the countable product — gives that these finite-dimensional
divergences converge to `KL(P‖R)`.

This gives a version of `ChenGeorgiouPavon2021.energy_eq_klReal_via_embedding` for any path model
with a countable separating family of measurable readouts, such as continuous paths evaluated at
dense times via `exists_measurableEmbedding_nat_continuousMap`. The remaining hypothesis `hconv`
identifies the limit of the finite-dimensional divergences. -/
theorem toReal_klDiv_map_frestrictLe_tendsto_of_separating
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (φ : ℕ → E → ℝ) (hφ : ∀ n, Measurable (φ n))
    (hsep : Function.Injective (fun x => (fun n => φ n x : ℕ → ℝ)))
    (P R : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (hac : P ≪ R) (hfin : klDiv P R ≠ ⊤) :
    Tendsto (fun n => (klDiv
        (P.map (fun x => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (fun m => φ m x)))
        (R.map (fun x => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (fun m => φ m x)))).toReal)
      atTop (nhds (klDiv P R).toReal) := by
  set e : E → (ℕ → ℝ) := fun x n => φ n x with he_def
  have he : Measurable e := measurable_pi_lambda e (fun n => hφ n)
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hsep
  haveI : IsProbabilityMeasure (P.map e) := Measure.isProbabilityMeasure_map he.aemeasurable
  haveI : IsProbabilityMeasure (R.map e) := Measure.isProbabilityMeasure_map he.aemeasurable
  have hac' : P.map e ≪ R.map e := hac.map he
  have hfin' : klDiv (P.map e) (R.map e) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (klDiv_map_le P R hac e he)
  -- the embedding preserves KL (DPI both ways)
  have hemb_kl : (klDiv (P.map e) (R.map e)).toReal = (klDiv P R).toReal :=
    toReal_klDiv_map_eq_of_leftInverse P R hac hfin e he hemb.invFun hemb.measurable_invFun
      hemb.leftInverse_invFun
  -- finite-prefix restriction filtration on `ℕ → ℝ`
  let ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    { seq := fun n => MeasurableSpace.comap
        (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n) inferInstance
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
  have htends := klDiv_map_tendsto_toReal (P.map e) (R.map e) hac' hfin'
    (fun n => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
    (fun n => Preorder.measurable_frestrictLe n) ℱ (fun _ => rfl)
    iSup_comap_frestrictLe_eq_pi
  have hmapP : ∀ n, (P.map e).map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
      = P.map (fun x => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e x)) := fun n => by
    rw [Measure.map_map (Preorder.measurable_frestrictLe n) he]; rfl
  have hmapR : ∀ n, (R.map e).map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n)
      = R.map (fun x => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (e x)) := fun n => by
    rw [Measure.map_map (Preorder.measurable_frestrictLe n) he]; rfl
  simp only [hmapP, hmapR, hemb_kl] at htends
  exact htends

/-- **The continuum KL is the limit of grid-projected divergences through a separating family**
(convenience `=` form of `toReal_klDiv_map_frestrictLe_tendsto_of_separating`). If the grid
divergences also converge to `L`, then uniqueness of limits gives `L = KL(P‖R)`. The hypothesis
`hconv` supplies that second convergence statement. -/
theorem eq_toReal_klDiv_of_separating_tendsto
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (φ : ℕ → E → ℝ) (hφ : ∀ n, Measurable (φ n))
    (hsep : Function.Injective (fun x => (fun n => φ n x : ℕ → ℝ)))
    (P R : Measure E) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (hac : P ≪ R) (hfin : klDiv P R ≠ ⊤) (L : ℝ)
    (hconv : Tendsto (fun n => (klDiv
        (P.map (fun x => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (fun m => φ m x)))
        (R.map (fun x => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n (fun m => φ m x)))).toReal)
      atTop (nhds L)) :
    L = (klDiv P R).toReal :=
  tendsto_nhds_unique hconv
    (toReal_klDiv_map_frestrictLe_tendsto_of_separating φ hφ hsep P R hac hfin)

/-- **Continuum energy identity for the continuous-path model.**
For continuous-path laws `P ≪ R` on `C(T, ℝ)` (`T` compact, locally compact, second countable,
and nonempty) with finite KL, suppose the divergences of their finite-time marginals, sampled at
the first `n+1` points of `denseSeq T`, converge to `L`. Dense-time evaluation is a measurable
point-separating family (`continuous_eval_const` and `Continuous.ext_on`), so
`eq_toReal_klDiv_of_separating_tendsto` gives `L = KL(P‖R)`. The hypothesis `hconv` contains the
finite-dimensional KL-to-energy convergence supplied by the relevant Cameron--Martin or
Girsanov argument. -/
theorem eq_toReal_klDiv_continuousMap_of_tendsto
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [Nonempty T]
    [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
    (P R : Measure C(T, ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (hac : P ≪ R) (hfin : klDiv P R ≠ ⊤) (L : ℝ)
    (hconv : Tendsto (fun n => (klDiv
        (P.map (fun f => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n
          (fun m => f (TopologicalSpace.denseSeq T m))))
        (R.map (fun f => Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n
          (fun m => f (TopologicalSpace.denseSeq T m))))).toReal)
      atTop (nhds L)) :
    L = (klDiv P R).toReal := by
  have hφ : ∀ n, Measurable (fun f : C(T, ℝ) => f (TopologicalSpace.denseSeq T n)) :=
    fun n => (continuous_eval_const (TopologicalSpace.denseSeq T n)).measurable
  have hsep : Function.Injective
      (fun (f : C(T, ℝ)) => (fun n => f (TopologicalSpace.denseSeq T n) : ℕ → ℝ)) := by
    intro f f' hff
    apply DFunLike.coe_injective
    refine Continuous.ext_on (TopologicalSpace.denseRange_denseSeq T) f.continuous f'.continuous ?_
    rintro x ⟨n, rfl⟩
    exact congrFun hff n
  exact eq_toReal_klDiv_of_separating_tendsto
    (fun n f => f (TopologicalSpace.denseSeq T n)) hφ hsep P R hac hfin L hconv

end ForMathlib.MeasureTheory
