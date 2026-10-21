namespace OAI

namespace TwoPointCorrelations

lemma halasz_collision_algebra {k : ℕ} (hk : 0<k) {A B I C R : ℝ}
    (hA : 0<A) (hB : 0<B) (hC : 0≤C) (hR : C^2<R)
    (hdiag : R^k*B≤A) (hmoment : I^(2*k)≤A^(2*k-1)*B) : C*I<A := by
  by_contra hn
  have hAI : A≤C*I := le_of_not_gt hn
  have hpow := pow_le_pow_left₀ hA.le hAI (2*k)
  rw [mul_pow] at hpow
  have ha : A^(2*k) ≤ C^(2*k)*A^(2*k-1)*B := by
    calc
      A^(2*k) ≤ C^(2*k)*I^(2*k) := hpow
      _ ≤ C^(2*k)*(A^(2*k-1)*B) :=
        mul_le_mul_of_nonneg_left hmoment (pow_nonneg hC _)
      _ = _ := by ring
  have hb := halasz_collision_power_absorb (by omega : 1≤2*k) hA ha
  have hRpow : C^(2*k)<R^k := by
    rw [pow_mul]
    exact pow_lt_pow_left₀ hR (sq_nonneg C) (by omega)
  have hstrict : C^(2*k)*B<R^k*B := mul_lt_mul_of_pos_right hRpow hB
  linarith

end TwoPointCorrelations
end OAI
