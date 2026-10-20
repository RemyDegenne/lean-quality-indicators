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

lemma toCommaMorphism_eq_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) : f.toCommaMorphism = f.hom := rfl

end Comma
end Comma
end CategoryTheory.MorphismProperty
end
