@[expose] public section

universe w v u

namespace CategoryTheory

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section mateEquivSquareComp

variable {a b c d e f x y z : B}

variable {g₁ : a ⟶ d} {h₁ : b ⟶ e} {k₁ : c ⟶ f} {g₂ : d ⟶ x} {h₂ : e ⟶ y} {k₂ : f ⟶ z}

variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : b ⟶ c} {r₂ : c ⟶ b} {l₃ : d ⟶ e} {r₃ : e ⟶ d}

variable {l₄ : e ⟶ f} {r₄ : f ⟶ e} {l₅ : x ⟶ y} {r₅ : y ⟶ x} {l₆ : y ⟶ z} {r₆ : z ⟶ y}

variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

variable (adj₄ : l₄ ⊣ r₄) (adj₅ : l₅ ⊣ r₅) (adj₆ : l₆ ⊣ r₆)

section leftAdjointSquare.comp

variable (α : g₁ ≫ l₃ ⟶ l₁ ≫ h₁) (β : h₁ ≫ l₄ ⟶ l₂ ≫ k₁)

variable (γ : g₂ ≫ l₅ ⟶ l₃ ≫ h₂) (δ : h₂ ≫ l₆ ⟶ l₄ ≫ k₂)

/-- A square of squares between left adjoints can be composed by iterating vertical and horizontal
composition.
-/
def leftAdjointSquare.comp :
    ((g₁ ≫ g₂) ≫ (l₅ ≫ l₆)) ⟶ ((l₁ ≫ l₂) ≫ (k₁ ≫ k₂)) :=
  vcomp (hcomp α β) (hcomp γ δ)

end leftAdjointSquare.comp
end mateEquivSquareComp
end Bicategory
end CategoryTheory
end
