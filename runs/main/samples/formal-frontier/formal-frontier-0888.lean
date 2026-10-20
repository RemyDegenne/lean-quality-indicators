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

theorem tensorHomEquiv_symm_apply_apply {X : Scheme.{u}} (M N P : X.Modules)
    (g : (M.val ⊗ N.val) ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P.val) :
    tensorHomEquiv M N P ((tensorHomEquiv M N P).symm g) = g :=
  (tensorHomEquiv M N P).apply_symm_apply g

end AlgebraicGeometry.Scheme.Modules
end
