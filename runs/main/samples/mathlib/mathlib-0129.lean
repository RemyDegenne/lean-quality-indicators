@[expose] public section

universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

attribute [instance_reducible, instance 100] MonoidalClosed.closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

variable (A B : C) {X X' Y Y' Z : C}

variable [Closed A]

set_option quotPrecheck false in
notation A " ⟶[" C "] " B:10 => (@ihom C _ _ A _).obj B

open CategoryTheory.Limits

variable {A}

namespace MonoidalClosed

theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
  rfl

end MonoidalClosed
end CategoryTheory
end
