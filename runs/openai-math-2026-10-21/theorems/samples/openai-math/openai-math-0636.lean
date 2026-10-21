namespace OAI

noncomputable section

open CategoryTheory Limits

namespace LittleFinitistic.OrdinarySimulation.ChainAlgebra

universe u

variable (k : Type u) [Field k] (l : ℕ)

theorem resolutionDifferential_square (n : ℕ) :
    resolutionDifferential k l n ≫ resolutionDifferential k l (n+1) = 0 := by
  ext x
  change extendedArrow k l (n+1) * (extendedArrow k l n * x.val) = 0
  rw [← mul_assoc, extendedArrow_square, zero_mul]

end LittleFinitistic.OrdinarySimulation.ChainAlgebra
end
end OAI
