/-
# Sinkhorn / matrix scaling: existence of the discrete Schrödinger potentials (staging)

The **Sinkhorn–Knopp / matrix-scaling (DAD) existence theorem**: a strictly positive
kernel on a finite index set admits positive diagonal scalings realizing prescribed
positive marginals. Equivalently, the discrete Schrödinger system has a positive
solution. This is `ChenGeorgiouPavon2021`'s Theorem 8.1 (Fortet–IPF–Sinkhorn), stripped
of all Schrödinger-bridge specifics — it is a pure finite-dimensional fact.

Mathlib has the Birkhoff polytope / doubly-stochastic matrices
(`Analysis/Convex/Birkhoff`, `LinearAlgebra/Matrix/DoublyStochasticMatrix`) and
irreducible-matrix definitions (`LinearAlgebra/Matrix/Irreducible/Defs`) but NOT
Perron–Frobenius-as-a-theorem nor Sinkhorn scaling (grep-verified). Proposed home:
`Mathlib/LinearAlgebra/Matrix/SinkhornScaling.lean` (new). See `FOUNDATIONS.md` (Chain 3).

STATUS: `sorry` (staging target). Standard proofs go via a fixed point of the
Sinkhorn iteration (Hilbert projective metric / Birkhoff contraction) or a convex
program (min `∑ Gᵢⱼ φ̂ᵢ φⱼ` s.t. marginals); the Perron–Frobenius eigenvector is the
sub-lemma. A hard, self-contained target — a Fable ticket (F2).

FIX vs the paper scaffold: existence REQUIRES mass conservation `∑ᵢ pᵢ = ∑ⱼ qⱼ`
(the coupling `φ̂ᵢ Gᵢⱼ φⱼ` has total mass `∑ pᵢ` and `∑ qⱼ` simultaneously). The
earlier `ChenGeorgiouPavon2021.sinkhorn_potentials_exist` omitted this hypothesis and
was therefore under-specified; it is added here (`hsum`) and the paper library now
delegates to this corrected statement.
-/
import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace ForMathlib

/-- **Sinkhorn / matrix scaling — discrete Schrödinger potentials exist.** For a
finite index set, strictly positive marginals `p, q` with equal total mass, and a
strictly positive kernel `G`, there are strictly positive potential vectors
`φ0, φ̂0, φ1, φ̂1` solving the discrete Schrödinger system
`φ0 = G · φ1`, `φ̂1 = Gᵀ · φ̂0`, `φ0 ⊙ φ̂0 = p`, `φ1 ⊙ φ̂1 = q`
(uniqueness up to `φ ↦ αφ`, `φ̂ ↦ φ̂/α`). Chen–Georgiou–Pavon Theorem 8.1 /
Sinkhorn–Knopp. -/
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
  sorry

end ForMathlib
