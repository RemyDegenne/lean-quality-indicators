@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

/-- The integral singular chain complex of a topological space. -/
abbrev integralSingularChains (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integerCoefficients.{u}).obj X

end AlgebraicTopology
end
end
