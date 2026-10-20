public section

namespace LinearMap.BilinForm

open Module TauCeti.BilinForm

open LinearMap (BilinForm)

open scoped TensorProduct

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- The inclusion from determinant-one isometries to all isometries. -/
noncomputable def specialIsometryToIsometry (B : BilinForm R M) :
    specialIsometryGroup B →* isometryGroup B :=
  Subgroup.inclusion (specialIsometryGroup_le_isometryGroup B)

end CommRing
end LinearMap.BilinForm
end
