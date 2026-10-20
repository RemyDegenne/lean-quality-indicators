public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma finiteNegativeOneDeflationKernel_ι (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflationKernel A S T hST ≫
        kernel.ι (FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants T)) =
      kernel.ι (FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants S)) ≫
        finiteNegativeDeflationCoinvariants A S T hST := by
  simp [finiteNegativeOneDeflationKernel, kernelMapOfSquare]

end ContinuousGroupCohomology
end
