@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

@[reassoc]
theorem twoOpenDifference_comp_sum {X : TopCat.{u}} (U V : Opens X) :
    twoOpenDifferenceChainMap U V ≫ twoOpenSumChainMap U V = 0 := by
  simp only [twoOpenDifferenceChainMap, twoOpenSumChainMap,
    biprod.lift_desc, Preadditive.neg_comp, integralSingularChainMap,
    ← Functor.map_comp]
  rw [twoOpenIntersectionToLeft_comp, twoOpenIntersectionToRight_comp]
  exact add_neg_cancel _

end AlgebraicTopology
end
end
