@[expose] public section

noncomputable section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

variable (C) in
/-- The Dialectica category. An object of the category is a triple `⟨U, X, α ⊆ U × X⟩`,
and a morphism from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair `(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that
`{(u,y) | α(u, F(u, y))} ⊆ {(u,y) | β(f(u), y)}`. The subset `α` is actually encoded as an element
of `Subobject (U × X)`, and the above inequality is expressed using pullbacks. -/
structure Dial where
  /-- The source object -/
  src : C
  /-- The target object -/
  tgt : C
  /-- A subobject of `src ⨯ tgt`, interpreted as a relation -/
  rel : Subobject (src ⨯ tgt)

end CategoryTheory
end
end
