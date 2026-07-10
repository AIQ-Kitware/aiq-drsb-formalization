/-
# Sinkhorn / matrix scaling: existence of the discrete Schrödinger potentials

The **Sinkhorn–Knopp / matrix-scaling (DAD) existence theorem**: a strictly positive
kernel on a finite index set admits positive diagonal scalings realizing prescribed
positive marginals. Equivalently, the discrete Schrödinger system has a positive
solution. This is `ChenGeorgiouPavon2021`'s Theorem 8.1 (Fortet–IPF–Sinkhorn), stripped
of all Schrödinger-bridge specifics — it is a pure finite-dimensional fact.

Mathlib has the Birkhoff polytope / doubly-stochastic matrices
(`Analysis/Convex/Birkhoff`, `LinearAlgebra/Matrix/DoublyStochasticMatrix`) but NOT
Perron–Frobenius-as-a-theorem nor Sinkhorn scaling (grep-verified). Proposed home:
`Mathlib/LinearAlgebra/Matrix/SinkhornScaling.lean` (new). See `FOUNDATIONS.md` (Chain 3).

STATUS: **PROVED** (dependency-clean: propext / Classical.choice / Quot.sound only).

METHOD (no Brouwer / no Birkhoff contraction — Mathlib has neither): a **log-domain
convex minimization**. The scalings are read off the first-order conditions of
  ψ(b) = ∑ᵢ pᵢ·log(∑ⱼ Gᵢⱼ bⱼ) − ∑ⱼ qⱼ·log(bⱼ)
minimized over the open probability simplex. Existence of the minimizer is elementary:
`−qⱼ log bⱼ → +∞` at the boundary confines the sublevel set to an explicit compact set
`{b | ∀ j, δ ≤ bⱼ, ∑ b = 1}` (extreme value theorem, no coercivity lemma needed). The
scaling equations come from the 1-D directional derivatives along `eⱼ − eₖ`
(`IsLocalMin.hasDerivAt_eq_zero`); **mass conservation `∑ p = ∑ q` is exactly what forces
the Lagrange multiplier to vanish**, turning the stationarity condition into the two
marginal constraints.

FIX vs the paper scaffold: existence REQUIRES mass conservation `∑ᵢ pᵢ = ∑ⱼ qⱼ`
(the coupling `φ̂ᵢ Gᵢⱼ φⱼ` has total mass `∑ pᵢ` and `∑ qⱼ` simultaneously). The
earlier `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` omitted this hypothesis and
was therefore under-specified; it is added here (`hsum`) and the paper library now
delegates to this corrected statement.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Real Finset

namespace ForMathlib

/-- **[M1] Common column residual vanishes by mass conservation.** If a positive `b`
normalizes to `1`, the row relation `aᵢ·(∑ⱼ Gᵢⱼ bⱼ) = pᵢ` holds, the marginals have
equal total mass, and the column residual `(∑ᵢ aᵢ Gᵢⱼ) − qⱼ/bⱼ` is a single constant `μ`
independent of `j`, then `μ = 0`.

Construction-independent: it takes only the row relation `hrow`, never the objective,
`D2`, or the scaling `aa`. Extracted from `matrix_scaling_exists`; a self-contained
mass-balance fact. -/
private theorem common_column_residual_eq_zero
    {ι : Type*} [Fintype ι]
    (p q a b : ι → ℝ) (G : ι → ι → ℝ)
    (hb_ne : ∀ j, b j ≠ 0)
    (hb_sum : ∑ j, b j = 1)
    (hmass : ∑ i, p i = ∑ j, q j)
    (hrow : ∀ i, a i * ∑ j, G i j * b j = p i)
    (μ : ℝ)
    (hresid : ∀ j, (∑ i, a i * G i j) = μ + q j / b j) :
    μ = 0 := by
  have step : ∀ j, b j * (∑ i, a i * G i j) = μ * b j + q j := by
    intro j
    rw [hresid j, mul_add, mul_comm (b j) (q j / b j), div_mul_cancel₀ (q j) (hb_ne j)]
    ring
  have hsumL : ∑ j, b j * (∑ i, a i * G i j) = ∑ i, p i := by
    have e1 : ∀ j, b j * (∑ i, a i * G i j) = ∑ i, a i * (G i j * b j) := by
      intro j; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hrow i, Finset.mul_sum]
  have hsumR : ∑ j, b j * (∑ i, a i * G i j) = μ * (∑ j, b j) + ∑ j, q j := by
    rw [Finset.sum_congr rfl (fun j _ => step j), Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hb_sum, mul_one] at hsumR
  linarith [hsumL, hsumR, hmass]

/-- **[M2] Zero column residual gives the column scaling equation.** From `bⱼ ≠ 0` and
`(∑ᵢ aᵢ Gᵢⱼ) − qⱼ/bⱼ = 0`, conclude `bⱼ·(∑ᵢ Gᵢⱼ aᵢ) = qⱼ`. Pure finite algebra;
extracted from `matrix_scaling_exists`. -/
private theorem column_scaling_of_zero_residual
    {ι : Type*} [Fintype ι]
    (q a b : ι → ℝ) (G : ι → ι → ℝ)
    (hb_ne : ∀ j, b j ≠ 0)
    (hresid : ∀ j, (∑ i, a i * G i j) - q j / b j = 0) :
    ∀ j, b j * ∑ i, G i j * a i = q j := by
  intro j
  have hbne : b j ≠ 0 := hb_ne j
  have hval : (∑ i, a i * G i j) = q j / b j := by linarith [hresid j]
  rw [show (∑ i, G i j * a i) = (∑ i, a i * G i j) from
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  rw [hval]
  field_simp

/-- **[M3a] Directional-variation pairwise residual equality.** At a positive interior
minimizer `bs` of the log-domain objective `ψ` over the truncated simplex `K`, the column
residual `(∑ᵢ aaᵢ Gᵢⱼ) − qⱼ/bsⱼ` (with `aaᵢ = pᵢ / ∑ⱼ Gᵢⱼ bsⱼ`) takes the same value at
every pair `j, j₀`.

This is the analytic core of `matrix_scaling_exists`: the first-order condition of `ψ`
restricted to the line `bs + t·(eⱼ − e_{j₀})`. `ψ` and the feasible set `K` are
reconstructed inline from the primary data `(p, q, G, δ)`; only the `IsMinOn` witness is
assumed. No positivity of `p, q` is needed — they enter only as coefficients. -/
private theorem stationarity_pairwise_residual_eq
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (G : ι → ι → ℝ) (hG : ∀ i j, 0 < G i j)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (bs : ι → ℝ) (hbs_gt : ∀ l, δ < bs l) (hbs_sum : ∑ l, bs l = 1)
    (hbs_min : IsMinOn
      (fun b => (∑ i, p i * Real.log (∑ j, G i j * b j)) - ∑ j, q j * Real.log (b j))
      {b | (∀ l, δ ≤ b l) ∧ ∑ l, b l = 1} bs)
    (j j₀ : ι) :
    (∑ i, (p i / (∑ jj, G i jj * bs jj)) * G i j) - q j / bs j
      = (∑ i, (p i / (∑ jj, G i jj * bs jj)) * G i j₀) - q j₀ / bs j₀ := by
  classical
  have hbs_pos : ∀ l, 0 < bs l := fun l => lt_trans hδ_pos (hbs_gt l)
  set ψ : (ι → ℝ) → ℝ :=
    fun b => (∑ i, p i * Real.log (∑ j, G i j * b j)) - ∑ j, q j * Real.log (b j) with hψ
  set K : Set (ι → ℝ) := {b | (∀ l, δ ≤ b l) ∧ ∑ l, b l = 1} with hK
  set D2 : ι → ℝ := fun i => ∑ jj, G i jj * bs jj with hD2
  have hD2_pos : ∀ i, 0 < D2 i := fun i => by
    rw [hD2]; exact Finset.sum_pos (fun jj _ => mul_pos (hG i jj) (hbs_pos jj)) ⟨j, Finset.mem_univ j⟩
  set aa : ι → ℝ := fun i => p i / D2 i with haa
  set w : ι → ℝ := fun l => (if l = j then (1:ℝ) else 0) - (if l = j₀ then (1:ℝ) else 0) with hw
  have hwsum : ∑ l, w l = 0 := by simp [hw]
  have hc : ∀ i, ∑ j', G i j' * w j' = G i j - G i j₀ := by
    intro i
    simp only [hw, mul_sub, Finset.sum_sub_distrib]
    simp
  set Fc : ℝ → ℝ := fun t =>
    (∑ i, p i * Real.log (D2 i + t * (G i j - G i j₀)))
      - (∑ l, q l * Real.log (bs l + t * w l)) with hFc
  have hinner : ∀ (t : ℝ) i, (∑ j', G i j' * (bs j' + t * w j')) = D2 i + t * (G i j - G i j₀) := by
    intro t i
    have hstep : (∑ j', G i j' * (bs j' + t * w j'))
        = (∑ j', G i j' * bs j') + t * (∑ j', G i j' * w j') := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j' _; ring
    rw [hstep, hc i]
  have hFct : ∀ t, Fc t = ψ (fun l => bs l + t * w l) := by
    intro t
    simp only [hFc, hψ]
    have hpart : (∑ i, p i * Real.log (D2 i + t * (G i j - G i j₀)))
        = ∑ i, p i * Real.log (∑ j', G i j' * (bs j' + t * w j')) := by
      apply Finset.sum_congr rfl; intro i _; rw [hinner t i]
    rw [hpart]
  have hFc0 : Fc 0 = ψ bs := by
    have hbs_eq : (fun l => bs l + (0:ℝ) * w l) = bs := by funext l; ring
    rw [hFct 0, hbs_eq]
  have heventK : ∀ᶠ t in nhds (0:ℝ), (fun l => bs l + t * w l) ∈ K := by
    have hsum_t : ∀ t : ℝ, ∑ l, (bs l + t * w l) = 1 := by
      intro t
      rw [Finset.sum_add_distrib, hbs_sum, ← Finset.mul_sum, hwsum, mul_zero, add_zero]
    have hfloor : ∀ᶠ t in nhds (0:ℝ), ∀ l, δ ≤ bs l + t * w l := by
      rw [Filter.eventually_all]
      intro l
      have hcont : ContinuousAt (fun t : ℝ => bs l + t * w l) 0 := by fun_prop
      have h0 : δ < bs l + (0:ℝ) * w l := by
        have he : bs l + (0:ℝ) * w l = bs l := by ring
        rw [he]; exact hbs_gt l
      have hmem : {t : ℝ | δ < bs l + t * w l} ∈ nhds (0:ℝ) :=
        hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds h0)
      filter_upwards [hmem] with t ht
      exact le_of_lt ht
    filter_upwards [hfloor] with t ht
    exact ⟨ht, hsum_t t⟩
  have hlm : IsLocalMin Fc 0 := by
    have hev : ∀ᶠ t in nhds (0:ℝ), Fc 0 ≤ Fc t := by
      filter_upwards [heventK] with t ht
      rw [hFc0, hFct t]
      exact isMinOn_iff.mp hbs_min _ ht
    exact hev
  have hlog_i : ∀ i, HasDerivAt (fun t => Real.log (D2 i + t * (G i j - G i j₀)))
      ((G i j - G i j₀) / (D2 i + 0 * (G i j - G i j₀))) 0 := by
    intro i
    refine HasDerivAt.log ((hasDerivAt_mul_const (G i j - G i j₀)).const_add (D2 i)) ?_
    show D2 i + (0:ℝ) * (G i j - G i j₀) ≠ 0
    simp only [zero_mul, add_zero]; exact (hD2_pos i).ne'
  have hlog_l : ∀ l, HasDerivAt (fun t => Real.log (bs l + t * w l))
      (w l / (bs l + 0 * w l)) 0 := by
    intro l
    refine HasDerivAt.log ((hasDerivAt_mul_const (w l)).const_add (bs l)) ?_
    show bs l + (0:ℝ) * w l ≠ 0
    simp only [zero_mul, add_zero]; exact (hbs_pos l).ne'
  have hd1 : HasDerivAt (fun t => ∑ i, p i * Real.log (D2 i + t * (G i j - G i j₀)))
      (∑ i, p i * ((G i j - G i j₀) / (D2 i + 0 * (G i j - G i j₀)))) 0 :=
    HasDerivAt.fun_sum (fun i _ => (hlog_i i).const_mul (p i))
  have hd2 : HasDerivAt (fun t => ∑ l, q l * Real.log (bs l + t * w l))
      (∑ l, q l * (w l / (bs l + 0 * w l))) 0 :=
    HasDerivAt.fun_sum (fun l _ => (hlog_l l).const_mul (q l))
  have hderiv : HasDerivAt Fc
      ((∑ i, p i * ((G i j - G i j₀) / (D2 i + 0 * (G i j - G i j₀))))
        - (∑ l, q l * (w l / (bs l + 0 * w l)))) 0 := by
    rw [hFc]; exact hd1.sub hd2
  have hval0 := hlm.hasDerivAt_eq_zero hderiv
  simp only [zero_mul, add_zero] at hval0
  have e1 : (∑ i, p i * ((G i j - G i j₀) / D2 i))
      = (∑ i, aa i * G i j) - (∑ i, aa i * G i j₀) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [haa]
    have hne := (hD2_pos i).ne'
    field_simp
  have e2 : (∑ l, q l * (w l / bs l)) = q j / bs j - q j₀ / bs j₀ := by
    have hpoint : ∀ l, q l * (w l / bs l)
        = (if l = j then q l / bs l else 0) - (if l = j₀ then q l / bs l else 0) := by
      intro l
      simp only [hw]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun l _ => hpoint l), Finset.sum_sub_distrib]
    simp
  rw [e1, e2] at hval0
  show (∑ i, aa i * G i j) - q j / bs j = (∑ i, aa i * G i j₀) - q j₀ / bs j₀
  linarith [hval0]

/-- **Matrix scaling / Sinkhorn existence.** For a strictly positive kernel `G` on a
finite index set and strictly positive marginals `p, q` of equal total mass, there exist
strictly positive scalings `a, b` with `aᵢ·(∑ⱼ Gᵢⱼ bⱼ) = pᵢ` and `bⱼ·(∑ᵢ Gᵢⱼ aᵢ) = qⱼ`.

Proved via log-domain minimization; see the module docstring. Dependency-clean; a genuine
Mathlib gap (Sinkhorn/matrix scaling is not in Mathlib). -/
theorem matrix_scaling_exists {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hsum : ∑ i, p i = ∑ j, q j)
    (G : ι → ι → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∃ a b : ι → ℝ, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      (∀ i, a i * ∑ j, G i j * b j = p i) ∧
      (∀ j, b j * ∑ i, G i j * a i = q j) := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · exact ⟨fun _ => 1, fun _ => 1, fun i => isEmptyElim i, fun j => isEmptyElim j,
      fun i => isEmptyElim i, fun j => isEmptyElim j⟩
  -- nonempty case
  -- global minimum index for G
  obtain ⟨gmin, hgmin_pos, hgmin⟩ : ∃ c, 0 < c ∧ ∀ i j, c ≤ G i j := by
    obtain ⟨ij, -, hij⟩ := Finset.exists_min_image (Finset.univ : Finset (ι × ι))
      (fun ij => G ij.1 ij.2) Finset.univ_nonempty
    exact ⟨G ij.1 ij.2, hG _ _, fun i j => hij (i, j) (Finset.mem_univ _)⟩
  -- min of q
  obtain ⟨qq, hqq_pos, hqq⟩ : ∃ c, 0 < c ∧ ∀ j, c ≤ q j := by
    obtain ⟨j1, -, hj1⟩ := Finset.exists_min_image (Finset.univ : Finset ι) q Finset.univ_nonempty
    exact ⟨q j1, hq _, fun j => hj1 j (Finset.mem_univ _)⟩
  set P := ∑ i, p i with hP
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN_pos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set u : ι → ℝ := fun _ => N⁻¹ with hu
  have hu_pos : ∀ l, 0 < u l := fun l => by rw [hu]; positivity
  have hu_sum : ∑ l, u l = 1 := by
    rw [hu]; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hN]; field_simp
  set ψ : (ι → ℝ) → ℝ :=
    fun b => (∑ i, p i * Real.log (∑ j, G i j * b j)) - ∑ j, q j * Real.log (b j) with hψ
  -- lower bound helpers
  have hGb_ge : ∀ b : ι → ℝ, (∀ l, 0 ≤ b l) → (∑ l, b l = 1) → ∀ i, gmin ≤ ∑ j, G i j * b j := by
    intro b hb0 hb1 i
    calc gmin = ∑ j, gmin * b j := by rw [← Finset.mul_sum, hb1, mul_one]
      _ ≤ ∑ j, G i j * b j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hgmin i j) (hb0 j))
  have hGb_pos : ∀ b : ι → ℝ, (∀ l, 0 ≤ b l) → (∑ l, b l = 1) → ∀ i, 0 < ∑ j, G i j * b j :=
    fun b hb0 hb1 i => lt_of_lt_of_le hgmin_pos (hGb_ge b hb0 hb1 i)
  have hlb_p : ∀ b : ι → ℝ, (∀ l, 0 ≤ b l) → (∑ l, b l = 1) →
      P * Real.log gmin ≤ ∑ i, p i * Real.log (∑ j, G i j * b j) := by
    intro b hb0 hb1
    have h := hGb_ge b hb0 hb1
    rw [hP, Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (Real.log_le_log hgmin_pos (h i)) (le_of_lt (hp i)))
  -- upper bound for b coords on simplex
  have hle1 : ∀ b : ι → ℝ, (∀ l, 0 ≤ b l) → (∑ l, b l = 1) → ∀ j, b j ≤ 1 := by
    intro b hb0 hb1 j
    calc b j ≤ ∑ l, b l := Finset.single_le_sum (fun l _ => hb0 l) (Finset.mem_univ j)
      _ = 1 := hb1
  set M := ψ u - P * Real.log gmin with hM
  have hM_nonneg : 0 ≤ M := by
    rw [hM]
    have hup : ∀ l, (0:ℝ) ≤ u l := fun l => le_of_lt (hu_pos l)
    have hlb := hlb_p u hup hu_sum
    have hq_part : ∑ j, q j * Real.log (u j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j _
      apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hq j))
      rw [hu, Real.log_inv, neg_nonpos]
      apply Real.log_nonneg
      rw [hN]; have : (1:ℕ) ≤ Fintype.card ι := Fintype.card_pos; exact_mod_cast this
    have hψu : ψ u = (∑ i, p i * Real.log (∑ j, G i j * u j)) - ∑ j, q j * Real.log (u j) := by
      simp only [hψ]
    linarith [hlb, hq_part, hψu]
  set δ0 := Real.exp (-M / qq) with hδ0
  have hδ0_pos : 0 < δ0 := Real.exp_pos _
  set δ := min δ0 N⁻¹ / 2 with hδ
  have hmin_pos : 0 < min δ0 N⁻¹ := lt_min hδ0_pos (by positivity)
  have hδ_pos : 0 < δ := by rw [hδ]; linarith
  have hδ_lt_δ0 : δ < δ0 := by
    rw [hδ]; have := min_le_left δ0 N⁻¹; linarith
  have hδ_le_N : δ ≤ N⁻¹ := by
    rw [hδ]
    have h1 := min_le_right δ0 N⁻¹
    have h2 : (0:ℝ) ≤ N⁻¹ := by positivity
    linarith
  -- sublevel bound
  have hsublevel : ∀ b : ι → ℝ, (∀ l, 0 < b l) → (∑ l, b l = 1) → ψ b ≤ ψ u → ∀ j, δ0 ≤ b j := by
    intro b hbpos hbsum hble j
    have hb0 : ∀ l, 0 ≤ b l := fun l => le_of_lt (hbpos l)
    have hlb := hlb_p b hb0 hbsum
    have hψb : ψ b = (∑ i, p i * Real.log (∑ j, G i j * b j)) - ∑ l, q l * Real.log (b l) := by
      simp only [hψ]
    have hqsum_ge : - M ≤ ∑ l, q l * Real.log (b l) := by
      rw [hM]; linarith [hlb, hble, hψb]
    -- single term ≥ sum (all terms ≤ 0)
    have hsplit : ∑ l, q l * Real.log (b l)
        = q j * Real.log (b j) + ∑ l ∈ Finset.univ.erase j, q l * Real.log (b l) :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)).symm
    have htail : ∑ l ∈ Finset.univ.erase j, q l * Real.log (b l) ≤ 0 :=
      Finset.sum_nonpos (fun l _ => mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hq l))
        (Real.log_nonpos (le_of_lt (hbpos l)) (hle1 b hb0 hbsum l)))
    have hqj_ge : - M ≤ q j * Real.log (b j) := by linarith [hqsum_ge, hsplit, htail]
    have hlogb1 : -M / q j ≤ Real.log (b j) := by
      rw [div_le_iff₀ (hq j)]; linarith [hqj_ge, mul_comm (q j) (Real.log (b j))]
    have hlogb2 : -M / qq ≤ -M / q j := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      gcongr
      exact hqq j
    rw [hδ0, ← Real.exp_log (hbpos j)]
    apply Real.exp_le_exp.mpr
    linarith [hlogb1, hlogb2]
  -- the compact feasible set
  set K : Set (ι → ℝ) := {b | (∀ l, δ ≤ b l) ∧ ∑ l, b l = 1} with hK
  have hu_mem : u ∈ K := ⟨fun l => by rw [hu]; exact hδ_le_N, hu_sum⟩
  have hK_closed : IsClosed K := by
    rw [hK, Set.setOf_and]
    refine IsClosed.inter ?_ ?_
    · rw [Set.setOf_forall]
      exact isClosed_iInter (fun l => isClosed_le continuous_const (continuous_apply l))
    · exact isClosed_eq (continuous_finsetSum _ (fun l _ => continuous_apply l)) continuous_const
  have hK_bdd : Bornology.IsBounded K := by
    apply (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset
    intro b hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro l
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨by linarith [hb1 l, hδ_pos], ?_⟩
    calc b l ≤ ∑ m, b m :=
          Finset.single_le_sum (fun m _ => le_of_lt (lt_of_lt_of_le hδ_pos (hb1 m))) (Finset.mem_univ l)
      _ = 1 := hb2
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
  have hψ_cont : ContinuousOn ψ K := by
    rw [hψ]
    apply ContinuousOn.sub
    · apply continuousOn_finsetSum
      intro i _
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log
      · exact (continuous_finsetSum _
          (fun j _ => continuous_const.mul (continuous_apply j))).continuousOn
      · intro b hb
        obtain ⟨hb1, hb2⟩ := hb
        exact ne_of_gt (hGb_pos b (fun l => le_of_lt (lt_of_lt_of_le hδ_pos (hb1 l))) hb2 i)
    · apply continuousOn_finsetSum
      intro j _
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log
      · exact (continuous_apply j).continuousOn
      · intro b hb
        obtain ⟨hb1, hb2⟩ := hb
        exact ne_of_gt (lt_of_lt_of_le hδ_pos (hb1 j))
  obtain ⟨bs, hbs_mem, hbs_min⟩ := hK_compact.exists_isMinOn ⟨u, hu_mem⟩ hψ_cont
  have hbs_ge_δ : ∀ l, δ ≤ bs l := hbs_mem.1
  have hbs_sum : ∑ l, bs l = 1 := hbs_mem.2
  have hbs_pos : ∀ l, 0 < bs l := fun l => lt_of_lt_of_le hδ_pos (hbs_ge_δ l)
  have hbs_le_u : ψ bs ≤ ψ u := isMinOn_iff.mp hbs_min u hu_mem
  have hbs_ge_δ0 : ∀ j, δ0 ≤ bs j := hsublevel bs hbs_pos hbs_sum hbs_le_u
  -- row marginals of bs
  set D2 : ι → ℝ := fun i => ∑ j, G i j * bs j with hD2
  have hD2_pos : ∀ i, 0 < D2 i := fun i => by
    rw [hD2]; exact hGb_pos bs (fun l => le_of_lt (hbs_pos l)) hbs_sum i
  -- the scaling a
  set aa : ι → ℝ := fun i => p i / D2 i with haa
  have haa_pos : ∀ i, 0 < aa i := fun i => by rw [haa]; exact div_pos (hp i) (hD2_pos i)
  -- fix a base index
  obtain ⟨j0⟩ := hne
  -- KEY: the residual `(∑ i, aa i * G i j) - q j / bs j` is independent of `j` (M3a);
  -- `hbs_gt : δ < bs l` comes from `δ < δ0 ≤ bs l`, and ψ/K are reconstructed inside M3a.
  have key : ∀ j, (∑ i, aa i * G i j) - q j / bs j
      = (∑ i, aa i * G i j0) - q j0 / bs j0 := fun j =>
    stationarity_pairwise_residual_eq p q G hG δ hδ_pos bs
      (fun l => lt_of_lt_of_le hδ_lt_δ0 (hbs_ge_δ0 l)) hbs_sum hbs_min j j0
  -- the common column residual `μ`, constant in `j` by `key`, packaged as `∑ = μ + q/bs`
  set μ := (∑ i, aa i * G i j0) - q j0 / bs j0
  have hresid : ∀ j, (∑ i, aa i * G i j) = μ + q j / bs j := fun j => by
    have hk := key j; linarith [hk]
  -- row marginals `aaᵢ·(∑ⱼ Gᵢⱼ bsⱼ) = pᵢ`, by construction of `aa := p / D2`
  have hrow : ∀ i, aa i * ∑ j, G i j * bs j = p i := by
    intro i
    show aa i * D2 i = p i
    rw [haa]
    show p i / D2 i * D2 i = p i
    exact div_mul_cancel₀ (p i) (ne_of_gt (hD2_pos i))
  -- mass conservation forces the residual to vanish (M1)
  have hμ : μ = 0 :=
    common_column_residual_eq_zero p q aa bs G
      (fun j => ne_of_gt (hbs_pos j)) hbs_sum hsum hrow μ hresid
  -- assemble: row equation is `hrow`; column equation is M2 on the `μ = 0` residual
  refine ⟨aa, bs, haa_pos, hbs_pos, hrow, ?_⟩
  have hzero : ∀ j, (∑ i, aa i * G i j) - q j / bs j = 0 := by
    intro j; rw [hresid j, hμ]; ring
  exact column_scaling_of_zero_residual q aa bs G (fun j => ne_of_gt (hbs_pos j)) hzero

/-- **Sinkhorn / matrix scaling — discrete Schrödinger potentials exist.** For a
finite index set, strictly positive marginals `p, q` with equal total mass, and a
strictly positive kernel `G`, there are strictly positive potential vectors
`φ0, φ̂0, φ1, φ̂1` solving the discrete Schrödinger system
`φ0 = G · φ1`, `φ̂1 = Gᵀ · φ̂0`, `φ0 ⊙ φ̂0 = p`, `φ1 ⊙ φ̂1 = q`
(uniqueness up to `φ ↦ αφ`, `φ̂ ↦ φ̂/α`). Chen–Georgiou–Pavon Theorem 8.1 /
Sinkhorn–Knopp.

Proved by reduction to `matrix_scaling_exists`: the scalings `a := φ̂0`, `b := φ1`
returned there make the coupling `φ̂0ᵢ Gᵢⱼ φ1ⱼ` have row sums `p` and column sums `q`;
the remaining two potentials are the row/column marginals `φ0ᵢ = ∑ⱼ Gᵢⱼ φ1ⱼ`,
`φ̂1ⱼ = ∑ᵢ Gᵢⱼ φ̂0ᵢ`. -/
theorem sinkhorn_potentials_exist {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hsum : ∑ i, p i = ∑ j, q j)                    -- mass conservation (NECESSARY)
    (G : ι → ι → ℝ) (hG : ∀ i j, 0 < G i j) :
    ∃ φ0 φhat0 φ1 φhat1 : ι → ℝ,
      (∀ i, 0 < φ0 i) ∧ (∀ i, 0 < φhat0 i) ∧ (∀ j, 0 < φ1 j) ∧ (∀ j, 0 < φhat1 j) ∧
      (∀ i, φ0 i = ∑ j, G i j * φ1 j) ∧            -- (8.4a)
      (∀ j, φhat1 j = ∑ i, G i j * φhat0 i) ∧      -- (8.4b)
      (∀ i, φ0 i * φhat0 i = p i) ∧                -- (8.4c)
      (∀ j, φ1 j * φhat1 j = q j) := by            -- (8.4d)
  obtain ⟨a, b, ha_pos, hb_pos, hrow, hcol⟩ := matrix_scaling_exists p q hp hq hsum G hG
  refine ⟨fun i => ∑ j, G i j * b j, a, b, fun j => ∑ i, G i j * a i,
    fun i => Finset.sum_pos (fun j _ => mul_pos (hG i j) (hb_pos j)) ⟨i, Finset.mem_univ i⟩,
    ha_pos, hb_pos,
    fun j => Finset.sum_pos (fun i _ => mul_pos (hG i j) (ha_pos i)) ⟨j, Finset.mem_univ j⟩,
    fun _ => rfl, fun _ => rfl, ?_, hcol⟩
  intro i
  show (∑ j, G i j * b j) * a i = p i
  linear_combination hrow i

end ForMathlib
