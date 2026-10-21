namespace OAI

namespace Yau.Waves

open Set Filter

open scoped Topology ContDiff

noncomputable section

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gaussian_absorbs_power (c : ℝ) (hc : 0 < c) (p K : ℝ) :
    ∀ᶠ N : ℝ in atTop,
      N ^ p * Real.exp (-c * N ^ (1 / 3 : ℝ)) ≤ N ^ (-K) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3 * (p + K)) c hc).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have he : ∀ᶠ N : ℝ in atTop,
      (N ^ (1 / 3 : ℝ)) ^ (3 * (p + K)) * Real.exp (-c * N ^ (1 / 3 : ℝ)) ≤ 1 :=
    ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with N hN hpos
  have heq : (N ^ (1 / 3 : ℝ)) ^ (3 * (p + K)) = N ^ (p + K) := by
    rw [← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [heq] at hN
  rw [Real.rpow_neg hpos.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hpos K)]
  simpa [Real.rpow_add hpos, mul_assoc, mul_left_comm, mul_comm] using hN

end
end Yau.Waves
end OAI
