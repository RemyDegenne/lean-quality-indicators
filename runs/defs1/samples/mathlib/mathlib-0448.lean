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

variable (L R P Q W)

variable {L R P Q W}

variable (L R P Q W)

/-- The forgetful functor from the full subcategory of `Comma L R` defined by `P` is
fully faithful. -/
def forgetFullyFaithful : (forget L R P ⊤ ⊤).FullyFaithful where
  preimage {X Y} f := ⟨f, trivial, trivial⟩

end Comma
end Comma
end CategoryTheory.MorphismProperty
end
