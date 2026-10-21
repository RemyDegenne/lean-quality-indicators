namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem noapprox_threshold_numerics
    (K s t : ℝ) (hK : 2 ≤ K) (ht : s / (2 * K) ≤ t)
    (hlarge : 4 * K ^ 127942 < s) :
    0 < s ∧ 2 < t ∧ K ^ 127940 * s < t ^ 2 ∧
      2 * (K ^ 527 * s) < t ^ 2 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hKone : 1 ≤ K := le_trans (by norm_num) hK
  have hs : 0 < s := lt_trans (mul_pos (by norm_num) (pow_pos hKpos _)) hlarge
  have hden : 0 < 2 * K := mul_pos (by norm_num) hKpos
  have hst : s ≤ 2 * K * t := by
    simpa only [mul_comm t] using (div_le_iff₀ hden).mp ht
  have hKpow : K ≤ K ^ 127942 := le_self_pow₀ hKone (by norm_num)
  have htlarge : 2 < t := by
    apply (mul_lt_mul_iff_right₀ hden).mp
    nlinarith only [hlarge, hKpow, hst]
  have hlong : K ^ 127940 * s < t ^ 2 :=
    pow_mul_lt_sq_of_popular_lower K s t 127940 hKpos hs ht hlarge
  have hpow : 2 * K ^ 527 ≤ K ^ 127940 := by
    calc
      2 * K ^ 527 ≤ K * K ^ 527 :=
        mul_le_mul_of_nonneg_right hK (pow_nonneg hKpos.le _)
      _ = K ^ 528 := (pow_succ' K 527).symm
      _ ≤ K ^ 127940 := pow_le_pow_right₀ hKone (by norm_num)
  refine ⟨hs, htlarge, hlong, ?_⟩
  calc
    2 * (K ^ 527 * s) = (2 * K ^ 527) * s := by ring
    _ ≤ K ^ 127940 * s := mul_le_mul_of_nonneg_right hpow hs.le
    _ < t ^ 2 := hlong

end RyserCoveringCounterexample.Incidence
end OAI
