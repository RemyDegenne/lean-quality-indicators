@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The sign-free endomorphism induced from the swapped two-open cover: first
restrict antipodal negation to the south/north intersection, then forget the
order by the sign-free intersection swap map. -/
def sphere2PunctureIntersectionAntipodalInduced :
    TopCat.of sphere2PunctureIntersection ⟶
      TopCat.of sphere2PunctureIntersection :=
  AlgebraicTopology.twoOpenIntersectionMap sphere2Antipodal
      sphere2NorthPunctured sphere2SouthPunctured
      sphere2SouthPunctured sphere2NorthPunctured
      sphere2Antipodal_mapsTo_north_south
      sphere2Antipodal_mapsTo_south_north ≫
    AlgebraicTopology.twoOpenIntersectionSwapMap
      sphere2SouthPunctured sphere2NorthPunctured

end SphereTopology
end
end
