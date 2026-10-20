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

@[simp] theorem zero_tmul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (t : Γ(N, U)) : tmul M N U 0 t = 0 := by
  unfold tmul
  rw [TensorProduct.zero_tmul, map_zero]

end AlgebraicGeometry.Scheme.Modules
end
