@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- The two-point computation stated with the unlifted integer module as its
target. -/
noncomputable def reducedSingularHomologyZeroTwoPointIntegerIso :
    reducedSingularHomologyZero twoPointSpace ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyZeroTwoPointIso ≪≫
    singularHomologyIntegerCoefficientsIso

end TopCat
end
end
