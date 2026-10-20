set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.MorphismProperty

section Comma

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {T : Type*} [Category* T]
  (L : A ⥤ T) (R : B ⥤ T)

variable (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)

namespace Comma

variable {L R P Q W}

variable [Q.IsMultiplicative] [W.IsMultiplicative]

@[reassoc]
lemma comp_right {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

end Comma
end Comma
end CategoryTheory.MorphismProperty
end
