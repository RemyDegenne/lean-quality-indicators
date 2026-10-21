namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped Topology

namespace Problem336.SlopeReadout

theorem readout_observation {B : ℕ → ℝ} (x : Bool)
    (hB : Tendsto (slope B) atTop (nhds 0)) :
    readout (fun n => (n : ℝ) * (if x then 1 else 0) + B n) = x := by
  exact readout_of_tendsto_bool (tendsto_slope_observation hB)

end Problem336.SlopeReadout
end
end OAI
