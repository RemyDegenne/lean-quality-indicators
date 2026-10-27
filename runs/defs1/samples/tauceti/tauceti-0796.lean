public section

open AlgebraicGeometry CategoryTheory Matrix WithConv

open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The set of defining relations: the entries of the relation matrix. -/
noncomputable abbrev relationSet : Set (GeneralLinear.coordinateHopfAlgebra R (m + m)) :=
  ConstantForm.relationSet R (m + m) (JFin m R)

end TauCeti.Symplectic
end
