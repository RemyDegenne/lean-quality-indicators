@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] (A B : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The inverse tensor Hom maps, proven compatible with restrictions. -/
noncomputable def tensorPresheafHomEquiv (theta : A ⟶ B) (M : Presheaves A)
    (N : Presheaves B) :
    (tensorPresheaf A B theta M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N) where
  toFun := tensorPresheafHomDown A B theta M
  invFun := tensorPresheafHomUp A B theta M
  left_inv t := by
    apply PresheafOfModules.hom_ext
    intro U
    change (tensorSectionHomEquiv A B theta M U (N.obj U)).symm
      ((tensorSectionHomEquiv A B theta M U (N.obj U)) (t.app U)) = t.app U
    exact (tensorSectionHomEquiv A B theta M U (N.obj U)).symm_apply_apply _
  right_inv g := by
    apply PresheafOfModules.hom_ext
    intro U
    change (tensorSectionHomEquiv A B theta M U (N.obj U))
      ((tensorSectionHomEquiv A B theta M U (N.obj U)).symm (g.app U)) = g.app U
    exact (tensorSectionHomEquiv A B theta M U (N.obj U)).apply_symm_apply _

end RingedSpaces.Modules
end
