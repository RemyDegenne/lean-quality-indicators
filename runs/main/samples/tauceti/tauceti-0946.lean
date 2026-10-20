public section

universe w' v u

namespace TauCeti

open CategoryTheory Category Limits Preadditive

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type w'} [Semiring R] [Linear R C]
  {w : R} {X Y Z : CurvedDuplex C w}

attribute [local simp] Hom.comm₀ Hom.comm₁ Hom.comm₀_assoc Hom.comm₁_assoc

@[reassoc]
theorem comp_nullHomotopicMap (f : X ⟶ Y) (h₀ : Y.X₀ ⟶ Z.X₁) (h₁ : Y.X₁ ⟶ Z.X₀) :
    f ≫ nullHomotopicMap h₀ h₁ = nullHomotopicMap (f.f₀ ≫ h₀) (f.f₁ ≫ h₁) := by
  ext <;> simp [comp_add]

end CurvedDuplex
end TauCeti
end
