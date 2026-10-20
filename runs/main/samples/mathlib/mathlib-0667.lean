@[expose] public section

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open ENNReal (ofReal)

open scoped ENNReal NNReal Topology

namespace Real

variable {ι : Type*} [Fintype ι]

@[simp]
theorem volume_real_Ico {a b : ℝ} : volume.real (Ico a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']

end Real
end
end
