@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C]
  (A B : Cᵒᵖ ⥤ CommRingCat.{u}) (theta : A ⟶ B)

/-- The right-order component of `rightPresheafMap` on one open. -/
noncomputable def rightSectionMap {M N : Presheaves A} (h : M ⟶ N)
    (U : Cᵒᵖ) :
    rightSectionCat A B theta M U ⟶ rightSectionCat A B theta N U :=
  (rightSectionIso A B theta M U).hom ≫ tensorSectionMap A B theta h U ≫
    (rightSectionIso A B theta N U).inv

end RingedSpaces.Modules
end
