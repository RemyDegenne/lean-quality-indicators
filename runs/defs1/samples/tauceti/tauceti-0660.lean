public section

open Metric Module MulOpposite Quaternion

open scoped RealInnerProductSpace RightActions Manifold ContDiff

namespace TauCeti

variable {E : Type*}

section Frame

variable [SMul ℍᵐᵒᵖ E]

/-- The three vectors `x <• i`, `x <• j`, `x <• k` obtained from `x` by right multiplication by
the imaginary quaternion units. On the unit sphere they are three pointwise orthonormal tangent
vector fields. -/
def quaternionFrame (x : E) : Fin 3 → E :=
  ![x <• (⟨0, 1, 0, 0⟩ : ℍ), x <• (⟨0, 0, 1, 0⟩ : ℍ), x <• (⟨0, 0, 0, 1⟩ : ℍ)]

end Frame
end TauCeti
end
