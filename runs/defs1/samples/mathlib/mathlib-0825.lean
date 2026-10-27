set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.MorphismProperty

section Comma

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {T : Type*} [Category* T]
  (L : A ⥤ T) (R : B ⥤ T)

section

variable {W : MorphismProperty T} {X : T}

/-- The object property on `Over X` induced by a morphism property. -/
def overObj (W : MorphismProperty T) {X : T} : ObjectProperty (Over X) := fun f ↦ W f.hom

end
end Comma
end CategoryTheory.MorphismProperty
end
