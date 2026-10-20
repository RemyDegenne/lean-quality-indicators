@[expose] public section

open CategoryTheory TopologicalSpace

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
theorem tensorSheafAdjunction_unit (theta : A ⟶ B) (M : Sheaves A)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    ((tensorSheafAdjunction A B theta).unit.app M).val.app U m =
      (PresheafOfModules.Hom.app
        ((moduleSheafificationAdjunction B).unit.app
          (tensorPresheaf A.obj B.obj theta.hom M.val)) U)
        (tensorUnitSection A.obj B.obj theta.hom M.val U m) := by
  change (tensorSectionHomEquiv A.obj B.obj theta.hom M.val U _)
      (PresheafOfModules.Hom.app
        ((moduleSheafificationAdjunction B).unit.app
          (tensorPresheaf A.obj B.obj theta.hom M.val)) U) m = _
  exact tensorSectionHomEquiv_apply A.obj B.obj theta.hom M.val U _ _ m

end RingedSpaces.Modules
end
