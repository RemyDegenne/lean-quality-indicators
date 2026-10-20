public section

open Bundle Manifold Set

open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section OfRiemannianMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The metric space structure associated to a Riemannian metric on a preconnected manifold,
obtained from `EMetricSpace.ofRiemannianMetric` now that the extended distance is known to be
finite. As for the extended version, the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory, one
should rather assume that there is an already existing metric space structure, satisfying
additionally the predicate `IsRiemannianManifold I M`. -/
-- The body is exposed because the characteristic property of the construction, that the topology
-- it induces is the manifold topology, is a definitional equality: a consumer installing this
-- structure on a manifold must unfold it to keep the charted-space instances of that topology.
@[expose, reducible] def MetricSpace.ofRiemannianMetric [T3Space M] [PreconnectedSpace M] :
    MetricSpace M :=
  letI : EMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.toMetricSpace (fun x y ↦ Manifold.riemannianEDist_ne_top I x y)

end OfRiemannianMetric
end TauCeti
end
end
