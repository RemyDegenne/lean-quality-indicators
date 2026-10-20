namespace P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough

set_option autoImplicit false

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup

open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace LiNormSq

open CuspForm.PeterssonCoset

section main

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ} {ℓ : ℕ}

theorem dens_slash {β : GL (Fin 2) ℝ} (hβ : 0 < (β.det : ℝ)) (F : ℍ → ℂ) (x : ℍ) :
    dens k (F ∣[k] β) x = (β.det : ℝ) ^ (k - 2) * dens k F (β • x) := by
  have h := UpperHalfPlane.petersson_slash k F F β x
  rw [UpperHalfPlane.σ, if_pos hβ, abs_of_pos hβ, petersson_self_eq_dens, petersson_self_eq_dens] at h
  simp only [ContinuousAlgEquiv.refl_apply] at h
  exact_mod_cast h

end main
end LiNormSq
end
end P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
