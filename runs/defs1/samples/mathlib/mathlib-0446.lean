@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory.Prod

namespace Prod

/-- `sectL C Z` is the functor `C ⥤ C × D` given by `X ↦ (X, Z)`. -/
@[simps]
def sectL (C : Type u₁) [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (Z : D) : C ⥤ C × D where
  obj X := (X, Z)
  map f := f ×ₘ 𝟙 Z

end Prod
end CategoryTheory
end
