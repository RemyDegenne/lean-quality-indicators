@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

variable {R X : Scheme.{u}} {p₁ p₂ : R ⟶ X}

variable [Flat p₁] [IsFinite p₁]

/-- The canonical finite indexing type of ranks occurring on a compact
target. -/
@[instance_reducible]
noncomputable def finrankRangeFintype [LocallyOfFinitePresentation p₁]
    [CompactSpace X] : Fintype (Set.range p₁.finrank) :=
  (finite_range_finrank (p₁ := p₁)).fintype

end AlgebraicGeometry.EquivalenceRelation
end
end
