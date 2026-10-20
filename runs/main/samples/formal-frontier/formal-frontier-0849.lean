@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

theorem isZero_reducedSingularHomologyZero_of_contractible (X : TopCat.{u})
    [ContractibleSpace (X : Type u)] :
    IsZero (reducedSingularHomologyZero X) :=
  isZero_reducedSingularHomologyZero_of_pathConnected X

end TopCat
end
end
