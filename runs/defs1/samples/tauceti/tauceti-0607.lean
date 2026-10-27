public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing LieRing.instLieAlgebra

/-- The integral Cartan generators on `V(ϖ₁) ⊕ V(ϖ₆)`. -/
def cartanGeneratorMatrix (i : Fin 6) :
    Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℤ :=
  Matrix.fromBlocks (TauCeti.E6Minuscule.cartanGeneratorMatrix i) 0 0
    (-TauCeti.E6Minuscule.cartanGeneratorMatrix i)

end TauCeti.E6DoubledMinuscule
end
