@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation.Restrict

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

@[reassoc]
lemma compositionConeToOriginal_snd (h : EquivalenceRelation p₁ p₂)
    (U : X.Opens) (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    compositionConeToOriginal h U hU ≫ h.c.snd =
      (compositionCone U hU).snd ≫ (p₁ ⁻¹ᵁ U).ι := by
  exact h.isLimit.fac _ WalkingCospan.right

end AlgebraicGeometry.EquivalenceRelation.Restrict
end
end
