public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
lemma pOpcycles_tateOpcyclesIsoNegOne_hom (M : Rep R G) :
    (tateComplex M).pOpcycles (-1) ≫ (tateOpcyclesIsoNegOne M).hom =
      (tateDNegTwoArrowIso M).hom.right ≫ (groupHomology.shortComplexH0 M).g := by
  exact CokernelCofork.π_mapOfIsColimit (φ := (tateDNegTwoArrowIso M).hom) _ _

end FiniteGroupTateCohomology
end
