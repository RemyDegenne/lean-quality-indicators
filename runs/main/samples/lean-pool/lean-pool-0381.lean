@[expose] public section

namespace NavierStokes.SpatialLocalization

noncomputable section

open ProblemStatement Set Filter

open AxisymmetricFields (projection)

open scoped ContDiff Topology

theorem periodicVelocity_origin (A : VelocityField) (t : ℝ) :
    periodicVelocity A (t, 0) = SpatialCurl.spatialCurl A (t, 0) :=
  periodicVelocity_eq A zero_mem_plateau

end
end NavierStokes.SpatialLocalization
end
