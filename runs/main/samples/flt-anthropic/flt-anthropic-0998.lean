namespace P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_1728

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace A1728Aux

open Polynomial

theorem isUnit_Δ_famJ1728 {W₀ : Type*} [CommRing W₀] (A : W₀) (h2 : IsUnit (2 : W₀)) (hA : IsUnit A) :
    IsUnit (famJ1728 A).Δ := by
  rw [PowerSeries.isUnit_iff_constantCoeff, famJ1728, Δ_short]
  simp only [map_sub, map_mul, map_pow, map_neg, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
    map_ofNat]
  rw [zero_pow two_ne_zero, mul_zero, sub_zero]
  have h64 : IsUnit (64 : W₀) := by
    have : (64 : W₀) = 2 ^ 6 := by norm_num
    rw [this]; exact h2.pow 6
  rw [neg_mul]
  exact (h64.mul (hA.pow 3)).neg

end A1728Aux
end P2MW.S_WeierstrassCurve_exists_powerSeries_lift_coeff_nthSeries_sub_mul_X_mem_span_and_jOfUnit_sub_eq_mul_X_pow_of_five_le_of_j_eq_1728
