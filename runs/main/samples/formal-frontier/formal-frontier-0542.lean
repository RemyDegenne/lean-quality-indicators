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
theorem tensorSheafAdjunction_counit (theta : A ⟶ B) (N : Sheaves B)
    (U : Cᵒᵖ) (b : B.obj.obj U) (n : N.val.obj U) :
    ((tensorSheafAdjunction A B theta).counit.app N).val.app U
        ((PresheafOfModules.Hom.app
          ((moduleSheafificationAdjunction B).unit.app
            (tensorPresheaf A.obj B.obj theta.hom
              ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N).val)) U)
          (b • tensorUnitSection A.obj B.obj theta.hom
            ((SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N).val U n)) =
      b • n := by
  let M := (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N
  let P := tensorPresheaf A.obj B.obj theta.hom M.val
  let element := b • tensorUnitSection A.obj B.obj theta.hom M.val U n
  have hAdj : sheafCounitPresheafMap A B theta N =
      (moduleSheafificationAdjunction B).unit.app P ≫
        ((SheafOfModules.forget (ringSheaf B)) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
            ((tensorSheafAdjunction A B theta).counit.app N) :=
    (moduleSheafificationAdjunction B).homEquiv_unit P N
      ((tensorSheafAdjunction A B theta).counit.app N)
  calc
    _ = (sheafCounitPresheafMap A B theta N).app U element := by
      have hEval := congrArg (fun h : P ⟶ N.val => h.app U element) hAdj
      exact hEval.symm
    _ = b • n := by
      rw [sheafCounitPresheafMap_eq]
      exact tensorPresheafAdjunction_counit A.obj B.obj theta.hom N.val U b n

end RingedSpaces.Modules
end
