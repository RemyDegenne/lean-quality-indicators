public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing LieRing.instLieAlgebra

@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreE ℚ (CartanMatrix.E 6)ᵀ i) = raisingMatrixQ i :=
  TauCeti.serreLift_serreE isSerreSystemQ i

end TauCeti.E6DoubledMinuscule
end
