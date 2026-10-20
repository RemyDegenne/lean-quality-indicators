@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] (A B : Cᵒᵖ ⥤ CommRingCat.{u})

set_option backward.isDefEq.respectTransparency false in
theorem tensorPresheafHomUp_smul (theta : A ⟶ B) (M : Presheaves A)
    {N : Presheaves B}
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N)
    (U : Cᵒᵖ) (b : B.obj U) (m : M.obj U) :
    letI : Module (B.obj U)
      (((PresheafOfModules.restrictScalars (ringMap A B theta)).obj N).obj U) :=
      (N.obj U).isModule
    (tensorPresheafHomUp A B theta M g).app U
        (b • tensorUnitSection A B theta M U m) = b • g.app U m := by
  let : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
  let : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
  change (tensorSectionHomEquiv A B theta M U (N.obj U)).symm (g.app U)
    (b • tensorUnitSection A B theta M U m) = _
  rw [map_smul, tensorSectionHomEquiv_symm_unit]
  rfl

end RingedSpaces.Modules
end
