public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

section OfDiscrete

variable {G} {k : Type*} [Ring k] [TopologicalSpace k] (X : TopRep k G) [DiscreteTopology X.V]

attribute [local instance] TopRep.distribMulAction

variable [ContinuousSMul G X.V]

/-- The explicit `H²` of the carrier of a discrete smooth representation `X` over any scalars, with
the action read off from `X`, is Mathlib's `continuousCohomology 2 X`. -/
noncomputable def _root_.TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete
    [LocallyCompactSpace G] :
    H2 G X.V ≃+ continuousCohomology 2 X :=
  (explicitH2AddEquivContinuousCohomology G X.V).trans (ofDiscreteModuleRestrictScalarsIntEquiv X 2)

end OfDiscrete
end TauCeti.ContCohomology
end
