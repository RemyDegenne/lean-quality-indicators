public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothnessThree

local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- The adjoint representation valued in bounded operators. -/
def continuousAdjointRepresentation : ContRepresentation ℝ G (LeftInvariantDerivation I G) :=
  ContinuousLinearEquiv.congr (derivationModelEquiv (I := I) (G := G)).symm
    (modelAdjointRepresentation (I := I) (G := G))

end TauCeti.Lie
end
end
