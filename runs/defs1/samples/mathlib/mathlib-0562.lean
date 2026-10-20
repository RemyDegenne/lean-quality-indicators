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

section Functoriality

variable {L R P Q W}

variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

/-- Lift a functor `F : C ⥤ Comma L R` to the subcategory `P.Comma L R Q W` under
suitable assumptions on `F`. -/
@[simps obj_toComma map_hom]
def lift {C : Type*} [Category* C] (F : C ⥤ Comma L R)
    (hP : ∀ X, P (F.obj X).hom)
    (hQ : ∀ {X Y} (f : X ⟶ Y), Q (F.map f).left)
    (hW : ∀ {X Y} (f : X ⟶ Y), W (F.map f).right) :
    C ⥤ P.Comma L R Q W where
  obj X :=
    { __ := F.obj X
      prop := hP X }
  map {X Y} f :=
    { __ := F.map f
      prop_hom_left := hQ f
      prop_hom_right := hW f }

end Functoriality
end Comma
end Comma
end CategoryTheory.MorphismProperty
end
