namespace OAI

namespace Erdos3

open scoped BigOperators

theorem flat_weighted_pointwise_le {A B d epsilon delta W M : ℝ}
    (hA : 0 ≤ A ∧ A ≤ W) (hB : 0 ≤ B ∧ B ≤ W) (hd : 0 ≤ d ∧ d ≤ M)
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta)) :
    (A - (1 + epsilon) * B) * d ≤ (1 + 2 * delta) * (A - B) +
      W * (M + 2) * (if 2 * delta < |d - 1| then (1 : ℝ) else 0) := by
  by_cases hbad : 2 * delta < |d - 1|
  · simp only [hbad, ite_true, mul_one]
    have hW : 0 ≤ W := hA.1.trans hA.2
    have hAd : A * d ≤ W * M := mul_le_mul hA.2 hd.2 hd.1 hW
    have hBweight : (1 + 2 * delta) * B ≤ 2 * W :=
      mul_le_mul (by linarith) hB.2 hB.1 (by norm_num)
    have hAnonneg : 0 ≤ (1 + 2 * delta) * A := mul_nonneg (by linarith) hA.1
    have hnegative : 0 ≤ ((1 + epsilon) * B) * d :=
      mul_nonneg (mul_nonneg (by linarith) hB.1) hd.1
    nlinarith
  · simp only [hbad, ite_false, mul_zero, add_zero]
    obtain ⟨hlo, hhi⟩ := abs_le.mp (le_of_not_gt hbad)
    have hAd : A * d ≤ A * (1 + 2 * delta) := mul_le_mul_of_nonneg_left (by linarith) hA.1
    have hBd : (1 + epsilon) * B * (1 - 2 * delta) ≤ (1 + epsilon) * B * d :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hB.1)
    have hBcoeff := mul_le_mul_of_nonneg_right hcoeff hB.1
    nlinarith

end Erdos3
end OAI
