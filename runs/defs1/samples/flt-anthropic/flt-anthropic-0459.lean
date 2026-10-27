namespace P2MW.S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le

set_option autoImplicit false

open scoped MatrixGroups

open Matrix MulAction Polynomial

namespace KleinFixedPointCount

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

def Omega (G : Type*) [Group G] (X : Type*) [MulAction G X] : SubMulAction G X where
  carrier := {x : X | ∃ g : G, g ≠ 1 ∧ g • x = x}
  smul_mem' := by
    rintro a x ⟨g, hg1, hgx⟩
    refine ⟨a * g * a⁻¹, ?_, ?_⟩
    · intro h
      apply hg1
      have h' : a⁻¹ * (a * g * a⁻¹) * a = a⁻¹ * 1 * a := by rw [h]
      simpa [mul_assoc] using h'
    · rw [mul_smul, mul_smul, inv_smul_smul, hgx]

end KleinFixedPointCount
end P2MW.S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
