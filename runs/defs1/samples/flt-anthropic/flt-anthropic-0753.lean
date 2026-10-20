namespace P2MW.S_CohCarrier_heckeT_diamondRaw_comm

set_option autoImplicit false

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

p2m_reactivate

namespace IharaSolComm

open scoped MatrixGroups

section DockHeckeT

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

def alpha : GL (Fin 2) ℚ where
  val := !![1, 0; 0, (ℓ : ℚ)]
  inv := !![1, 0; 0, (ℓ : ℚ)⁻¹]
  val_inv := by
    have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [hℓ]
  inv_val := by
    have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [hℓ]

end DockHeckeT
end IharaSolComm
end P2MW.S_CohCarrier_heckeT_diamondRaw_comm
