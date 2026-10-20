public section

open CategoryTheory TensorProduct

namespace TauCeti

universe u v w

variable (R : Type u) [CommRing R]

variable (H : Type v) [CommRing H] [HopfAlgebra R H]

/-- Finitely generated point representations and finitely generated comodules form equivalent
categories. Over a field, this is the representation--comodule equivalence for finite-dimensional
representations. -/
noncomputable def fgPointRepresentationCategoryEquivalence :
    FGPointRepresentationCat.{u, v, w} R H ≌ FGComoduleCat.{u, v, w} R H :=
  (PointRepresentationCat.toComodule R H).asEquivalence.congrFullSubcategory <| by
    ext V
    simp only [ObjectProperty.prop_inverseImage_iff, Functor.asEquivalence_functor,
      PointRepresentationCat.toComodule_obj_isFG_iff]

end TauCeti
end
