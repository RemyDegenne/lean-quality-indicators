public section

open CategoryTheory WithConv

namespace TauCeti

namespace SpecialLinear

universe u v w

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The special-linear coordinate Hopf algebra bundled with its finite-type algebra property. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  FiniteTypeCommHopfAlgCat.quotient
    (⟨GeneralLinear.coordinateHopfAlgebra R n,
      inferInstanceAs (Algebra.FiniteType R (GeneralLinear.coordinateHopfAlgebra R n))⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R n)

end SpecialLinear
end TauCeti
end
