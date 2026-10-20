@[expose] public section

noncomputable section

namespace EulerPacketSourceParameterScales

open Real EulerScale EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketBaseGuardScales

theorem monomial_le_polynomialFactor (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (n p q : ℕ) (hp : p ≤ 20) (hq : q ≤ 1000) :
    ((J+n : ℕ) : ℝ)^p*(scaleSequence J X n)^q ≤ polynomialFactor J X n := by
  have hj : (1 : ℝ) ≤ (J+n : ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
  have hx := sequence_one_le J hJ X hX n
  exact mul_le_mul (pow_le_pow_right₀ hj hp) (pow_le_pow_right₀ hx hq)
    (pow_nonneg (zero_le_one.trans hx) q) (pow_nonneg (zero_le_one.trans hj) 20)

end EulerPacketSourceParameterScales
end
end
