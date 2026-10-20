@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

theorem integralSingularHomologyMap_sphere2Antipodal_two :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.integralSingularChainMap sphere2Antipodal) 2 =
      -𝟙 _ := by
  let _ := sphere2MayerVietorisδOne_reversed_isIso
  exact
    AlgebraicTopology.integralSingularHomologyMap_eq_neg_id_of_twoOpen_swap
      sphere2Antipodal sphere2SouthPunctured sphere2NorthPunctured
      sphere2Antipodal_mapsTo_south_north
      sphere2Antipodal_mapsTo_north_south
      sphere2Punctured_join_reversed sphere2Punctured_join 1
      (sphere2PunctureIntersectionAntipodal_homology_eq_id 1)

end SphereTopology
end
end
