@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

infixl:15 " ⊣₂ " => ParametrizedAdjunction

namespace ParametrizedAdjunction

variable {F G}

variable (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} {X₃ Y₃ : C₃}

/-- The bijection `((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃)`
given by an adjunction with a parameter `adj₂ : F ⊣₂ G`. -/
def homEquiv : ((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃) :=
  (adj₂.adj X₁).homEquiv _ _

end ParametrizedAdjunction
end CategoryTheory
end
