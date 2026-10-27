@[expose] public section

universe w v u

namespace CategoryTheory

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section conjugateEquiv_mateEquiv_vcomp

variable {a b c d : B}

variable {g : a ⟶ c} {h : b ⟶ d}

variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : a ⟶ b} {r₂ : b ⟶ a} {l₃ : c ⟶ d} {r₃ : d ⟶ c}

variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

/-- Composition of a conjugate square with a square between left adjoints. -/
def leftAdjointConjugateSquare.vcomp (α : l₂ ⟶ l₁) (β : g ≫ l₃ ⟶ l₂ ≫ h) :
    g ≫ l₃ ⟶ l₁ ≫ h :=
  β ≫ α ▷ h

end conjugateEquiv_mateEquiv_vcomp
end Bicategory
end CategoryTheory
end
