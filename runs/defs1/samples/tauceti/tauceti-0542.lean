public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti.ChainComplex

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

variable {Y₁ Y₂ Y₃ Y₄ : SSet.{w}} {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
  (φ₁ : X₁ ⟶ Y₁) (φ₂ : X₂ ⟶ Y₂) (φ₃ : X₃ ⟶ Y₃) (φ₄ : X₄ ⟶ Y₄)

variable (sq : IsPushout t l r b) [Mono t]

/-- The cochain Mayer–Vietoris connecting morphism `Hⁿ(X₁) ⟶ Hᵐ(X₄)`, where `n + 1 = m`: the
connecting morphism of the cochain Mayer–Vietoris short exact sequence. -/
def mayerVietorisCochainδ (n m : ℕ) (h : n + 1 = m := by lia) :
    ((X₁.chainComplex R).linearYonedaObj k M).homology n ⟶
      ((X₄.chainComplex R).linearYonedaObj k M).homology m :=
  (shortExact_mayerVietorisCochainShortComplex R k M sq).δ n m (by simpa)

end SSet
end
end
