@[expose] public section

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Imported FactorizationSystems declaration. -/
def orthogonalClass (L R : MorphismProperty C) :=
  ∀ ⦃A B X Y : C⦄ (l : A ⟶ B) (_ : L l) (r : X ⟶ Y) (_ : R r) , orthogonal l r

end CategoryTheory
end
