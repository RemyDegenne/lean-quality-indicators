public section

open AlgebraicGeometry CategoryTheory WithConv

open scoped CategoryTheory.MonObj TensorProduct

namespace TauCeti.GeneralLinear

universe u v w

variable {R κ : Type u} [CommRing R] {N : ℕ}

section WeightCocharacter

/-- The diagonal unit family `i ↦ t ^ w i` attached to integer weights. -/
def weightDiagonalUnits {A : Type v} [CommMonoid A] (w : Fin N → ℤ) :
    Aˣ →* (Fin N → Aˣ) :=
  MonoidHom.pi fun i ↦ zpowGroupHom (w i)

end WeightCocharacter
end TauCeti.GeneralLinear
end
