public section

open Polynomial

namespace TauCeti

theorem discriminant_and_sextic_do_not_distinguish_C5_D5 :
    (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).discr = 121 ^ 2 ∧
      (X ^ 5 - 5 * X - 12 : ℤ[X]).discr = 8000 ^ 2 ∧
      (resolventSextic (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1)).eval (-16) = 0 ∧
      (resolventSextic (X ^ 5 - 5 * X - 12)).eval 40 = 0 ∧
      (resolventSextic (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1)).discr ≠ 0 ∧
      (resolventSextic (X ^ 5 - 5 * X - 12)).discr ≠ 0 ∧
      HasGaloisLabel ((X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).map
          (Int.castRingHom ℚ)) (⟨0, by simp⟩ : TransitiveGroupIndex 5) ∧
      HasGaloisLabel ((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ))
        (⟨1, by simp⟩ : TransitiveGroupIndex 5) := by
  have hC5 := (hasSexticRoot_iff _ _).mp hasSexticRoot_X5_add_X4_sub_4X3_sub_3X2_add_3X_add_1
  have hD5 := (hasSexticRoot_iff _ _).mp hasSexticRoot_X_pow_five_sub_five_mul_X_sub_twelve
  exact ⟨discr_X5_add_X4_sub_4X3_sub_3X2_add_3X_add_1, discr_X_pow_five_sub_five_mul_X_sub_twelve,
    hC5.1, hD5.1, hC5.2, hD5.2, hasGaloisLabel_X5_add_X4_sub_4X3_sub_3X2_add_3X_add_1,
    hasGaloisLabel_X_pow_five_sub_five_mul_X_sub_twelve⟩

end TauCeti
end
