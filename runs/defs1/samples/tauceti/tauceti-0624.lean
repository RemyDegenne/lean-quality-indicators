public section

open CategoryTheory Matrix WithConv

namespace TauCeti.SpecialOrthogonal

universe u v w

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The special orthogonal subgroup scheme of `GL n`. -/
noncomputable def groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n)

end TauCeti.SpecialOrthogonal
end
