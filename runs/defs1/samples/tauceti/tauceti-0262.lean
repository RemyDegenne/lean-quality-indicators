public section

namespace TauCeti

open _root_.Matrix _root_.LieAlgebra.Orthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-- The coordinate-difference weight `εᵢ - εⱼ` on the split diagonal Cartan. -/
noncomputable def typeDWeightSub (i j : ι) : Module.Dual K (typeDDiagonalCartan K ι) :=
  typeDEpsilon i - typeDEpsilon j

end TauCeti
end
