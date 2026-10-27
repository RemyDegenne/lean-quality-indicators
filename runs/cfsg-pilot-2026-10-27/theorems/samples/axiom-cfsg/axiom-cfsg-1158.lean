public section

namespace CFSG.GH72

open Subgroup

open scoped commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G]

section Inv

variable {E : Subgroup G} (hE : Odd (Nat.card E)) {t : G} (ht : orderOf t = 2)
  (htE : t ∈ normalizer (E : Set G))

include hE ht htE

theorem inf_C_sup_commutator_zpowers_eq : E ⊓ C t ⊔ ⁅E, zpowers t⁆ = E := by
  refine le_antisymm (sup_le inf_le_left (commutator_zpowers_le_of_mem_normalizer htE)) ?_
  intro g hg
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ :=
    (OddInversion.odd_involution_product_decomposition hE ht htE).1.surjOn hg
  simp only at hcj
  rw [← hcj]
  exact mul_mem (le_sup_left (b := ⁅E, zpowers t⁆) hc)
    (le_sup_right (a := E ⊓ C t) (mem_commutator_zpowers_of_conj_eq_inv hE hj.1 hj.2))

end Inv
end CFSG.GH72
end
