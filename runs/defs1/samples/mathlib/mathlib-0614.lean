@[expose] public section

set_option mathlib.tactic.category.grind true

universe v u

namespace CategoryTheory

open Category

infixr:10 " ≅ " => Iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace Iso

infixr:80 " ≪≫ " => Iso.trans

attribute [local grind] Function.LeftInverse Function.RightInverse

/-- The bijection `(Z ⟶ X) ≃ (Z ⟶ Y)` induced by `α : X ≅ Y`. -/
@[implicit_reducible, to_dual (attr := simps) homFromEquiv
/-- The bijection `(X ⟶ Z) ≃ (Y ⟶ Z)` induced by `α : X ≅ Y`. -/]
def homToEquiv (α : X ≅ Y) {Z : C} : (Z ⟶ X) ≃ (Z ⟶ Y) where
  toFun f := f ≫ α.hom
  invFun g := g ≫ α.inv
  left_inv := by cat_disch
  right_inv := by cat_disch

end Iso
end CategoryTheory
end
