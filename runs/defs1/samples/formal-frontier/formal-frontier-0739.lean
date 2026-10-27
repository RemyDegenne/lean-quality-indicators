@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] (A B : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Restrict a presheaf Hom along the local unit `m ↦ 1 ⊗ m`. -/
noncomputable def tensorPresheafHomDown (theta : A ⟶ B) (M : Presheaves A)
    {N : Presheaves B}
    (t : tensorPresheaf A B theta M ⟶ N) :
    M ⟶ (PresheafOfModules.restrictScalars (ringMap A B theta)).obj N :=
  { app := fun U => tensorSectionHomEquiv A B theta M U (N.obj U) (t.app U)
    naturality := fun {U V} f => by
      ext m
      change tensorSectionHomEquiv A B theta M V (N.obj V) (t.app V) (M.map f m) =
        N.map f (tensorSectionHomEquiv A B theta M U (N.obj U) (t.app U) m)
      rw [tensorSectionHomEquiv_apply A B theta M V (N.obj V) (t.app V)
        (M.map f m)]
      rw [tensorSectionHomEquiv_apply A B theta M U (N.obj U) (t.app U) m]
      rw [← tensorRestriction_unit A B theta M f m]
      exact PresheafOfModules.naturality_apply t f (tensorUnitSection A B theta M U m) }

end RingedSpaces.Modules
end
