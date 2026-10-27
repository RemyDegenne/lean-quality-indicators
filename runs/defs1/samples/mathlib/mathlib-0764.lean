@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open CategoryTheory.Functor

namespace Join

@[inherit_doc] scoped infixr:30 " ⋆ " => Join

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

section Functoriality

variable {C D} {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

/-- A pair of functors ((C ⥤ E), (D ⥤ E')) induces a functor `C ⋆ D ⥤ E ⋆ E'`. -/
def mapPair (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') : C ⋆ D ⥤ E ⋆ E' :=
  mkFunctor (Fₗ ⋙ inclLeft _ _) (Fᵣ ⋙ inclRight _ _) { app := fun _ ↦ edge _ _ }

end Functoriality
end Join
end CategoryTheory
end
