@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

theorem reducedSingularHomologyZeroTwoPointIntegerIso_swap :
    reducedSingularHomologyZeroTwoPointIntegerIso.inv ≫
        reducedSingularHomologyZeroMap twoPointSwap ≫
        reducedSingularHomologyZeroTwoPointIntegerIso.hom =
      -(𝟙 (ModuleCat.of ℤ ℤ)) := by
  change singularHomologyIntegerCoefficientsIso.inv ≫
      twoPointReducedBasis ≫ reducedSingularHomologyZeroMap twoPointSwap ≫
      twoPointReducedCoordinate ≫ singularHomologyIntegerCoefficientsIso.hom =
    -(𝟙 (ModuleCat.of ℤ ℤ))
  rw [twoPointReducedBasis_swap_assoc]
  rw [Preadditive.neg_comp, twoPointReducedBasis_coordinate_assoc]
  simp

end TopCat
end
end
