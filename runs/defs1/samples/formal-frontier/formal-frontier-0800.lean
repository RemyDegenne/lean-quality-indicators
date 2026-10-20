@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)

/-- Transport the native `B(U)`-module structure onto the right-order tensor. -/
noncomputable abbrev rightModule (M : Presheaves A) (U : Cᵒᵖ) :
    Module ((ringPresheaf B).obj U) (rightSection A B theta M U) :=
  (rightSectionAddEquiv A B theta M U).module _

end RingedSpaces.Modules
end
