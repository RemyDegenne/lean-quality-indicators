@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology BigOperators

open NavierStokes.OutgoingSchedule

namespace NavierStokes.PulseAmplitude

theorem errorConstant_ge {P : ℝ} (hP : 0 < P) (m : ℝ) :
    prefixBoundConstant P m ≤ errorConstant P m ∧
      correctionEnergyConstant P m ≤ errorConstant P m ∧
      TailEnergyBounds.tailConstant / 2 ≤ errorConstant P m ∧
      OutgoingTail.flattenLength + 2 * TailEnergyBounds.tailConstant ≤ errorConstant P m := by
  unfold errorConstant
  have hp := prefixBoundConstant_pos P m
  have hc := correctionEnergyConstant_pos hP m
  have hf := OutgoingTail.flattenLength_pos
  have ht := TailEnergyBounds.tailConstant_pos
  constructor
  · linarith only [hc, hf, ht]
  constructor
  · linarith only [hp, hf, ht]
  constructor <;> linarith only [hp, hc, hf, ht]

end NavierStokes.PulseAmplitude
end
end
