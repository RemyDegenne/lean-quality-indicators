@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Linear spatial dilation used to compute the volumes of scaled balls. -/
def campanatoHolderVec3ScaleLinear (a : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  a • LinearMap.id

end CKN.Foundation.Parabolic
end
end
