@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

variable [Flat p₁] [IsFinite p₁]

@[simp]
lemma mem_finrankOpen [LocallyOfFinitePresentation p₁] (r : ℕ) (x : X) :
    x ∈ finrankOpen (p₁ := p₁) r ↔ p₁.finrank x = r :=
  Iff.rfl

end AlgebraicGeometry.EquivalenceRelation
end
end
