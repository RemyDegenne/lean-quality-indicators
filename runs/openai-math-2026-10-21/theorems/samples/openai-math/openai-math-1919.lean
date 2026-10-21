namespace OAI

section

namespace Erdos3

theorem roundedModelScale_le_exp (P : ℝ) (d : ℕ) :
    (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1) ≤
      Real.exp (44 + 6 * max P 0 + 94 * d) := by
  have h2 : (2 ^ 14 : ℝ) ≤ Real.exp 28 := by
    calc
      (2 ^ 14 : ℝ) ≤ (Real.exp 2) ^ 14 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (2 : ℝ)]) _
      _ = Real.exp 28 := by rw [← Real.exp_nat_mul]; norm_num
  have h16 : (16 : ℝ) ^ (d + 1) ≤ Real.exp (16 * ((d : ℝ) + 1)) := by
    calc
      (16 : ℝ) ^ (d + 1) ≤ (Real.exp 16) ^ (d + 1) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (16 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc
    (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1) ≤
        Real.exp 28 * (Real.exp (P + 13 * d)) ^ 6 * Real.exp (16 * ((d : ℝ) + 1)) := by
      gcongr
    _ = Real.exp (44 + 6 * P + 94 * d) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
      ring
    _ ≤ Real.exp (44 + 6 * max P 0 + 94 * d) := by
      apply Real.exp_le_exp.mpr
      nlinarith [le_max_left P 0]

end Erdos3
end
end OAI
