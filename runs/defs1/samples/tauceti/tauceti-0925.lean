public section

universe w' v u

namespace TauCeti

open CategoryTheory Category Limits Preadditive

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type w'} [Semiring R] [Linear R C]
  {w : R} {X Y Z : CurvedDuplex C w}

attribute [local simp] Hom.comm₀ Hom.comm₁ Hom.comm₀_assoc Hom.comm₁_assoc

/-- The **null-homotopic morphism** `d h + h d` attached to an odd map `h = (h₀, h₁)` from `X` to
`Y`. It commutes with the differentials because `X` and `Y` have the same curvature. -/
def nullHomotopicMap (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) : X ⟶ Y where
  f₀ := X.d₀ ≫ h₁ + h₀ ≫ Y.d₁
  f₁ := X.d₁ ≫ h₀ + h₁ ≫ Y.d₀
  comm₀ := by simp [add_comm]
  comm₁ := by simp [add_comm]

end CurvedDuplex
end TauCeti
end
