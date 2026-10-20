@[expose] public section

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerPressureSpatialRegularity
      EulerMetricTransport
  EulerLpCylinderTranslation EulerCylinderSobolevSpace EulerParameterWordGevrey

open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- A genuine smooth cylinder representative of the solved L² field. -/
def representative (u : LiftL2 period) (hu : SmoothOrbit period u) : LiftDomain period → Space :=
  Classical.choose (exists_smooth_representative period u hu)

end EulerCylinderSmoothOrbit
end
end
