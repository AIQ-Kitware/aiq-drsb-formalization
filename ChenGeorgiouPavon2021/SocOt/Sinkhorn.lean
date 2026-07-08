/-
# CGP finite Sinkhorn/Fortet-IPF wrapper

This module contains the finite Sinkhorn-potential existence wrapper delegated
to the paper-agnostic matrix-scaling theorem in `ForMathlib`.
-/

import ChenGeorgiouPavon2021.SocOt.EntropicOT

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ChenGeorgiouPavon2021

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
