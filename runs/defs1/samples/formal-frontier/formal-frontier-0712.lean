@[expose] public section

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Subfunctor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {G : D ⥤ Type w}

/-- Restrict a subfunctor to the objects and arrows selected by `J`. -/
def precomp (S : Subfunctor G) (J : C ⥤ D) : Subfunctor (J ⋙ G) where
  obj X := S.obj (J.obj X)
  map f := S.map (J.map f)

end CategoryTheory.Subfunctor
end
