@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The fixed-coordinate reduced integral homology computation
`H̃₂(S²; ℤ) ≅ ℤ` for the standard metric two-sphere.

The sphere-homology result is described in J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 14, §3. The proof here uses the project's ordered Mayer--Vietoris,
normalized equatorial deformation and fixed circle computation, over Mathlib's
singular homology; it supplies no comparison with May's based-relative model. -/
noncomputable def reducedSingularHomologyTwoSphereTwoIntegerIso :
    TopCat.reducedSingularHomology sphere2 2 ≅ ModuleCat.of ℤ ℤ :=
  sphere2ReducedMayerVietorisIso ≪≫
    TopCat.reducedSingularHomologyIsoOfHomotopyEquiv
      sphere2PunctureIntersectionSphere1HomotopyEquiv 1 ≪≫
    reducedSingularHomologyOneSphereOneIntegerIso

end SphereTopology
end
end
