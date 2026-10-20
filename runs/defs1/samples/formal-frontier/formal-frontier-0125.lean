@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

variable [Flat p₁] [IsFinite p₁]

/-- The rank-`r` fibre as an open subset of the target. This packages the
rank pieces of Stacks Project
[Lemma 39.23.3, tag 03BI](https://stacks.math.columbia.edu/tag/03BI)
under the explicit local finite presentation hypothesis. -/
def finrankOpen [LocallyOfFinitePresentation p₁] (r : ℕ) : X.Opens :=
  ⟨{x : X | p₁.finrank x = r}, (isClopen_finrank_fiber (p₁ := p₁) r).2⟩

end AlgebraicGeometry.EquivalenceRelation
end
end
