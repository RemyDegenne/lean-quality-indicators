namespace P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one

set_option autoImplicit false

set_option linter.unusedSectionVars false

open Matrix MatrixGroups Subgroup MulAction

noncomputable section

namespace OrbifoldSL2

section Main

variable (Γ : Subgroup SL(2, ℤ))

def θ : SL(2, ℤ) ⧸ Γ → Gp ⧸ Hm Γ :=
  Quotient.map' π fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem π h

end Main
end OrbifoldSL2
end
end P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one
