@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open scoped BigOperators

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The normalized finite law of forward seeds. -/
def exactForwardSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M) :
    FiniteEventLaw (ExactForwardSeed M) where
  weight := exactSeedWeight
  weight_nonneg := exactSeedWeight_nonneg
  weight_sum := exactSeedWeight_sum nonempty

end
end QuantumParallelRepetition
end
end
