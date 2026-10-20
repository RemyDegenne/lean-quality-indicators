@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation.Restrict

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

/-- The symmetry map restricted to the common relation preimage. -/
def symmetry (h : EquivalenceRelation p₁ p₂) (U : X.Opens)
    (hU : p₁ ⁻¹ᵁ U = p₂ ⁻¹ᵁ U) :
    (p₁ ⁻¹ᵁ U).toScheme ⟶ (p₁ ⁻¹ᵁ U).toScheme :=
  (isPullback_morphismRestrict p₁ U).lift (snd U hU)
    ((p₁ ⁻¹ᵁ U).ι ≫ h.s) (by
      rw [snd_ι, Category.assoc, h.symmetry₁])

end AlgebraicGeometry.EquivalenceRelation.Restrict
end
end
