public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix

variable {K : Type} [Field K]

theorem mul_eigenProj {τ : K} (hτ : τ ^ 3 = 1) {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 3 = 1)
    (k : Fin 3) : y * eigenProj τ y k = τ ^ (k : ℕ) • eigenProj τ y k := by
  have hα : (τ ^ (k : ℕ)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  have h2 : y * y = y ^ 2 := (sq y).symm
  have h3' : y * y ^ 2 = 1 := by rw [← pow_succ', hy]
  have hα3 : τ ^ (k : ℕ) * (τ ^ (k : ℕ)) ^ 2 = 1 := by rw [← pow_succ']; exact hα
  unfold eigenProj
  rw [Matrix.mul_smul, smul_comm]
  congr 1
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, smul_add, smul_smul, h2, h3', hα3,
    one_smul]
  rw [show τ ^ (k : ℕ) * τ ^ (k : ℕ) = (τ ^ (k : ℕ)) ^ 2 by ring]
  abel

end CFSG.RankThree.PartTwo.Sec4
end
