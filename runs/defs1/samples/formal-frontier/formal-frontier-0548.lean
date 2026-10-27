@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The reversed-cover circle computation, retained as an order/sign client.
Its coordinate still means upper minus lower; the ordered-cover swap
theorem below records the negation of the connecting morphism. -/
noncomputable def reducedSingularHomologyOneSphereOneIntegerIsoReversed :
    TopCat.reducedSingularHomology sphere1 1 ≅ ModuleCat.of ℤ ℤ :=
  AlgebraicTopology.twoOpenReducedMayerVietorisIsoOfAcyclicOpens
      circleWestPunctured circleEastPunctured circlePunctured_join_reversed
      (isZero_reducedSingularHomology_circleWestPunctured 0)
      (isZero_reducedSingularHomology_circleEastPunctured 0)
      (isZero_reducedSingularHomology_circleWestPunctured 1)
      (isZero_reducedSingularHomology_circleEastPunctured 1) ≪≫
    TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
      circlePunctureIntersectionReversedHomotopyEquiv 0 ≪≫
    TopCat.reducedSingularHomologyZeroTwoPointIntegerIso

end SphereTopology
end
end
