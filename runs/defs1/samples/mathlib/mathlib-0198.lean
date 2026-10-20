set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.MorphismProperty

section Comma

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {T : Type*} [Category* T]
  (L : A ⥤ T) (R : B ⥤ T)

variable (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)

namespace Comma

variable {L R P Q W}

/-- Composition of morphisms in `P.Comma L R Q W`. -/
@[simps]
def Hom.comp [Q.IsStableUnderComposition] [W.IsStableUnderComposition] {X Y Z : P.Comma L R Q W}
    (f : Comma.Hom X Y) (g : Comma.Hom Y Z) :
    Comma.Hom X Z where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  prop_hom_left := Q.comp_mem _ _ f.prop_hom_left g.prop_hom_left
  prop_hom_right := W.comp_mem _ _ f.prop_hom_right g.prop_hom_right

end Comma
end Comma
end CategoryTheory.MorphismProperty
end
