@[expose] public section

universe w' w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- We say that `G` is a separator if the functor `C(G, -)` is faithful. -/
def IsSeparator (G : C) : Prop :=
  ObjectProperty.IsSeparating (.singleton G)

end CategoryTheory
end
