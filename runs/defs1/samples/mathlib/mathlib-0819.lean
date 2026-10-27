@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

namespace Bicategory

@[inherit_doc] scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

section Composition

variable {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `Adjunction.comp`. -/
@[simp]
def compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
  𝟙 _ ⊗≫ g₂ ◁ adj₁.counit ▷ f₂ ⊗≫ adj₂.counit

end Composition
end Adjunction
end Bicategory
end CategoryTheory
end
