namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ μ R : Type*} [CommRing R]

theorem mulVec_constraintProjectionInput [Fintype ι] [Fintype μ]
    (S : Matrix κ (ι ⊕ μ) R) (y : μ → R) :
    S *ᵥ constraintProjectionInput (ι := ι) y = (fun i j => S i (Sum.inr j)) *ᵥ y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, constraintProjectionInput]

end Erdos3
end
end OAI
