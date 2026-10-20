namespace P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

universe u v

noncomputable section

open MvPowerSeries

open scoped TensorProduct

namespace P2mFV

section Comm

variable {k : Type u} [CommRing k] {n : ℕ} (F : MvFormalGroup n k)

theorem constantCoeff_θ₁ : ∀ t, constantCoeff (θ₁ F t) = 0 := by
  rintro (j | j)
  · exact constantCoeff_X _
  · show constantCoeff (rename _ (F.toPowerSeries j)) = 0
    rw [constantCoeff_rename, F.constantCoeff_eq_zero]

end Comm
end P2mFV
end
end P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
