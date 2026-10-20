public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

set_option backward.isDefEq.respectTransparency false in
/-- The map between cokernels of the two finite-group norms induced by the norm
compatibility square. -/
noncomputable def finiteZeroDeflationCokernel (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    cokernel (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S)) ⟶
      cokernel (FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants T)) := by
  let p := finiteNegativeDeflationCoinvariants A S T hST
  let q := (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom
  let f := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants S)
  let g := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants T)
  have w : p ≫ g = f ≫ q := finiteNegativeDeflationCoinvariants_norm A S T hST
  exact cokernelMapOfSquare p q f g w

end ContinuousGroupCohomology
end
