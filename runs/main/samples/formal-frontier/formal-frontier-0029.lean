@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)

theorem rightRestriction_comm (M : Presheaves A) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    (rightSectionIso A B theta M U).hom ≫ tensorRestriction A B theta M f =
      rightRestriction A B theta M f ≫
        (ModuleCat.restrictScalars ((ringPresheaf B).map f).hom).map
          (rightSectionIso A B theta M V).hom := by
  simp [rightRestriction, Category.assoc]

end RingedSpaces.Modules
end
