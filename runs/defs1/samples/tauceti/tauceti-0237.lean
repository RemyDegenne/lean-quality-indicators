public section

open scoped Matrix

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)

namespace Symmetry

/-- The identity symmetry of a minuscule weight table. -/
def identity : T.Symmetry where
  nodePerm := 1
  indexPerm := 1
  weight_apply := by simp
  cartanMatrix_apply := by simp

end Symmetry
end MinusculeWeightTable
end TauCeti
end
