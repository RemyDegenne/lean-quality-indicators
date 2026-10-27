public section

set_option warningAsError true

open CategoryTheory MonoidalCategory BraidedCategory TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

noncomputable local instance pointwiseMonoidalCategoryStruct (X : Scheme.{u}) :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategoryStruct (R := X.sheaf.obj)

noncomputable local instance pointwiseMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.sheaf.obj)

noncomputable local instance pointwiseSymmetricCategory (X : Scheme.{u}) :
    SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.sheaf.obj)

/-- The ambient tensor bifunctor on modules over `X`, obtained by pointwise
presheaf tensor followed by sheafification. -/
@[expose]
noncomputable def tensorFunctor (X : Scheme.{u}) :
    X.Modules × X.Modules ⥤ X.Modules := by
  letI : MonoidalCategoryStruct X.PresheafOfModules :=
    PresheafOfModulesOfCommRing.monoidalCategoryStruct (R := X.sheaf.obj)
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.sheaf.obj)
  letI : SymmetricCategory X.PresheafOfModules :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.sheaf.obj)
  exact (toPresheafOfModules X).prod (toPresheafOfModules X) ⋙
    MonoidalCategory.tensor X.PresheafOfModules ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

end AlgebraicGeometry.Scheme.Modules
end
