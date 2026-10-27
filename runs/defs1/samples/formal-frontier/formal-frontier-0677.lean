@[expose] public section

open CategoryTheory TopologicalSpace

open scoped Polynomial

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

open AlgebraicGeometry

universe w

open Module.FiniteProjective

open AlgebraicGeometry.AffineEquivalenceRelation

/-- The two coordinate maps on a restricted rank stratum retain the internal
equivalence relation after passing to affine `Spec` coordinates. -/
def appTopFinrankOpen {R X : Scheme.{w}} {p₁ p₂ : R ⟶ X}
    [Flat p₁] [IsFinite p₁] [LocallyOfFinitePresentation p₁] [IsAffine X]
    (h : EquivalenceRelation p₁ p₂) (r : ℕ) :
    let U := finrankOpen (p₁ := p₁) r
    EquivalenceRelation
      (Spec.map (p₁ ∣_ U).appTop)
      (Spec.map (morphismRestrictSnd h r).appTop) := by
  dsimp only
  let _ : IsAffine (finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_finrankOpen (p₁ := p₁) r
  let _ : IsAffine (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r) :=
    isAffineOpen_preimage_finrankOpen (p₁ := p₁) r
  exact appTop (equivalenceRelationFinrankOpen h r)

end AlgebraicGeometry.EquivalenceRelation
end
end
