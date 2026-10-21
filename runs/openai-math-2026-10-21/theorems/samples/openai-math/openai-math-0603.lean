namespace OAI

noncomputable section

open scoped Topology

open Filter

open Filter MeasureTheory

open UniformSpace

open scoped ContDiff

open MeasureTheory

open MeasureTheory Set

open MeasureTheory Set Filter

open scoped Topology Interval

open Set Filter

open UniformSpace Set

open UniformSpace Filter

open UniformSpace Filter Set

open UniformSpace Filter Set MeasureTheory

open scoped Topology ContDiff

open Filter MeasureTheory Set

open Filter Set

open Filter UniformSpace

open Set MeasureTheory

open Set

open MeasureTheory Filter

open Set MeasureTheory Filter UniformSpace

open Set UniformSpace

open Set UniformSpace Filter

open Set MeasureTheory Filter

open UniformSpace Set Filter

open UniformSpace Set

open UniformSpace Set

open scoped ContDiff

open UniformSpace

open scoped ContDiff

open scoped ContDiff

namespace StronglyRationalVOA.SmoothCircleLift

lemma pushDensity_pos (F : SmoothCircleLift) (k : ℕ) {g : ℝ → ℝ}
    (hg : ∀ x, 0 < g x) (x : ℝ) : 0 < F.pushDensity k g x :=
  mul_pos (pow_pos (F.derivative_positive _) k) (hg _)

end StronglyRationalVOA.SmoothCircleLift
end
end OAI
