@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- The basis vector `1 ↦ [false] - [true]` in reduced `H₀`. -/
noncomputable def twoPointReducedBasis :
    singularHomologyIntegerCoefficients ⟶ reducedSingularHomologyZero twoPointSpace :=
  kernel.lift
    (twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients)
    twoPointReducedBasisClass twoPointReducedBasisClass_augmentation

end TopCat
end
end
