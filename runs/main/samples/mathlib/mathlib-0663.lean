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

variable (A X)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma whiskerLeft_curry_ihom_ev_app (g : A ⊗ Y ⟶ X) :
    A ◁ curry g ≫ (ihom.ev A).app X = g := by
  simp [curry_eq]

end MonoidalClosed
end CategoryTheory
end
