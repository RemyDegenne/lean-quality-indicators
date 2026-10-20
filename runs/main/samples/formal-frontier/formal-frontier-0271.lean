public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

@[simp]
lemma tateDNegTwoArrowIso_hom_right (M : Rep R G) :
    (tateDNegTwoArrowIso M).hom.right = (groupHomology.chainsIso₀ M).hom := rfl

end FiniteGroupTateCohomology
end
