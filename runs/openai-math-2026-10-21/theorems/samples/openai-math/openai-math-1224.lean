namespace OAI

namespace Laughlin.Spin

open scoped BigOperators Matrix Kronecker

theorem totalWeight_diagonal (A B : ℕ) :
    totalWeight A B = Matrix.diagonal (fun i : SpinIndex A B =>
      (A : ℝ)+B-2*((i.1.val : ℝ)+i.2.val)) := by
  ext i j
  by_cases h₁ : i.1=j.1 <;> by_cases h₂ : i.2=j.2 <;>
    simp [totalWeight,weightMatrix,Matrix.kroneckerMap,
      Matrix.one_apply,Matrix.diagonal_apply,Prod.ext_iff,h₁,h₂]
  ring

end Laughlin.Spin
end OAI
