@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

theorem reducedSingularHomologyTwoSphereTwoIntegerIso_hom :
    reducedSingularHomologyTwoSphereTwoIntegerIso.hom =
      sphere2ReducedMayerVietorisIso.hom ≫
      (TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
        sphere2PunctureIntersectionSphere1HomotopyEquiv 1).hom ≫
      reducedSingularHomologyOneSphereOneIntegerIso.hom := by
  rfl

end SphereTopology
end
end
