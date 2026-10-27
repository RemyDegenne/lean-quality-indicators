namespace P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

universe u

open CategoryTheory CategoryTheory.Limits Opposite

universe w'

namespace RSmall

variable {C₀ : Type u} [SmallCategory C₀] (J₀ : GrothendieckTopology C₀)

section S2

variable {J₀}

variable (X : C₀ᵒᵖ ⥤ AddCommGrpCat.{u+1}) [∀ c : C₀ᵒᵖ, Small.{u} (X.obj c)]

noncomputable def shrinkPresheaf : C₀ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj c := AddCommGrpCat.of (Shrink.{u} (X.obj c))
  map {c c'} f := AddCommGrpCat.ofHom
    ((shrinkEquiv X c').toAddMonoidHom.comp ((X.map f).hom.comp (shrinkEquiv X c).symm.toAddMonoidHom))
  map_id c := by ext x; simp
  map_comp f g := by ext x; simp

end S2
end RSmall
end P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections
