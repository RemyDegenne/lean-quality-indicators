@[expose] public section

open Homogenization

open Set

open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

theorem flow_spatialFDeriv_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s t : ℝ) :
    Continuous (fun x => fderiv ℝ (fun y => X t y s) x) := by
  by_cases hst : s ≤ t
  · exact flow_spatialFDeriv_continuous_of_le hb hX s t hst
  · have hts : t ≤ s := le_of_not_ge hst
    let br := regularityReverseTimeField b
    let Xr := regularityReverseTimeFlow X
    have hbr : SmoothPeriodicField br := smoothPeriodicField_regularityReverseTime hb
    have hXr : AVenhance.IsFlow br Xr := isFlow_regularityReverseTime hX
    have hcont := flow_spatialFDeriv_continuous_of_le hbr hXr (-s) (-t) (by linarith)
    simpa [Xr, regularityReverseTimeFlow] using hcont

end AVenhance.Infra.Flow
end
