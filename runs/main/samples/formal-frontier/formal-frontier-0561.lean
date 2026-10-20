@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}
  [Flat p₁] [IsFinite p₁]

lemma isAffineOpen_preimage_finrankOpen [LocallyOfFinitePresentation p₁]
    [IsAffine X] (r : ℕ) :
    IsAffineOpen (p₁ ⁻¹ᵁ finrankOpen (p₁ := p₁) r) :=
  (isAffineOpen_finrankOpen (p₁ := p₁) r).preimage p₁

end AlgebraicGeometry.EquivalenceRelation
end
end
