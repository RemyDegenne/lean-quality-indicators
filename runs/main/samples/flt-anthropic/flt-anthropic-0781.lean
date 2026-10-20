set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory

open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace NumberField.SArchIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

theorem toSIdele_diagS_apply_inl_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : {v // v ∉ S}) :
    (toSIdele E K S).hom ((diagS E K S).hom x) (Sum.inl (Sum.inr v)) = 0 := rfl

end NumberField.SArchIdele
