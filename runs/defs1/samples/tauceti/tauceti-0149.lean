public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

namespace TriangleGroup

/-- The spherical signature `(2, 3, 4)` is the symmetric group `S₄`: the octahedral
representation is an isomorphism. -/
noncomputable def equivOctahedral : TriangleGroup 2 3 4 ≃* Perm (Fin 4) :=
  have := finite_two_three_four
  ((MulEquiv.ofBijective octahedralRep.rangeRestrict
    (octahedralRep.rangeRestrict_surjective.bijective_of_nat_card_le
      (by rw [natCard_two_three_four, natCard_range_octahedralRep]))).trans
    (MulEquiv.subgroupCongr range_octahedralRep)).trans Subgroup.topEquiv

end TriangleGroup
end TauCeti
end
