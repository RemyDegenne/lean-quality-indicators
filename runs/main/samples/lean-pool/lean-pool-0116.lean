@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace Zeta32.Analytic.EnergyI

noncomputable section

section uC

variable {a : ℝ}

theorem uC_zero (ha : 0 < a) : uC a 0 = a := by
  unfold uC; simp [Real.sqrt_sq ha.le]

end uC
end
end Zeta32.Analytic.EnergyI
end
