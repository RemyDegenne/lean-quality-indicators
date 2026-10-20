public section

open scoped OnePoint

open Module

namespace TauCeti

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]

namespace Slope

/-- The slope represented by a primitive class `v : M`. -/
def mk (v : M) (h : IsPrimitive v) : Slope M := Quotient.mk (slopeSetoid M) ⟨v, h⟩

end Slope
end TauCeti
end
