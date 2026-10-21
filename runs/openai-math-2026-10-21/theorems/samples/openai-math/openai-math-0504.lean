namespace OAI

namespace ContingencyTables

open scoped BigOperators

open LinearMap (BilinForm)

section TwoLevel

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

lemma diagonalMatrix_form (κ x y : I → ℝ) :
    (Matrix.diagonal κ).toBilin' x y = ∑ i, κ i * x i * y i := by
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

end TwoLevel
end ContingencyTables
end OAI
