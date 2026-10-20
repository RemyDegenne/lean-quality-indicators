@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation.Restrict

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

@[reassoc]
lemma transitivity_ι (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    transitivity h U hU ≫ (p₁ ⁻¹ᵁ U).ι =
      compositionConeToOriginal h U hU ≫ h.t := by
  exact (isPullback_morphismRestrict p₁ U).lift_snd _ _ _

end AlgebraicGeometry.EquivalenceRelation.Restrict
end
end
