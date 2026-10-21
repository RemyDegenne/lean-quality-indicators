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

open UniformSpace Filter

open scoped Topology

open UniformSpace

open Filter MeasureTheory

open scoped Topology

namespace StronglyRationalVOA.SymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma conjugation_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) (x : H) :
    ‖conjugation T hs Q t x‖ ≤ ‖Q‖*‖x‖ := by
  change ‖flow T hs t (Q (flow T hs (-t) x))‖ ≤ _
  rw [flow_norm]
  simpa only [flow_norm] using Q.le_opNorm (flow T hs (-t) x)

end StronglyRationalVOA.SymmetricOperator
end
end OAI
