public section

set_option warningAsError true

open CategoryTheory MonoidalCategory TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategoryStruct (R := X.sheaf.obj)

private noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.sheaf.obj)

private noncomputable local instance (X : Scheme.{u}) :
    SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.sheaf.obj)

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Restriction along an open immersion commutes with the ambient module tensor,
naturally in both module arguments. -/
noncomputable def restrictTensorNatIso :
    tensorFunctor Y ⋙ restrictFunctor f ≅
      (restrictFunctor f).prod (restrictFunctor f) ⋙ tensorFunctor X :=
  (tensorRestrictNatIso f).symm

end
end AlgebraicGeometry.Scheme.Modules
end
