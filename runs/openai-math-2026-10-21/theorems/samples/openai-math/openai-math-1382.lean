namespace OAI

noncomputable section

namespace RealDeligneDrinfeld

namespace Differentiation

open FreeDerivations

variable {M N : Type} [LieRing M] [LieAlgebra ℝ M] [LieRing N] [LieAlgebra ℝ N]

@[simp] theorem slope_y (a b da db : M) : slope y a b da db = db := by simp [slope]

end Differentiation
end RealDeligneDrinfeld
end
end OAI
