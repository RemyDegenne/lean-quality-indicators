public section

namespace TauCeti

open Finset

universe u v w x

namespace NumericalType

attribute [instance] componentFintype componentDecidableEq componentNonempty

variable (T : NumericalType.{u})

@[simp]
lemma intersection_mulVec_multiplicity :
    T.intersection.mulVec (fun i ↦ (T.multiplicity i : ℤ)) = 0 := by
  funext i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using T.fiber_relation i

end NumericalType
end TauCeti
end
