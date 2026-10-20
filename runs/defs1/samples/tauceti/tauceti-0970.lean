public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ConstantForm

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

variable (C : Matrix (Fin n) (Fin n) R)

/-- The subgroup scheme of `GL n` preserving `C`. -/
noncomputable abbrev groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

end TauCeti.ConstantForm
end
