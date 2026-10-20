public section

noncomputable section

open Set ENNReal

namespace MeasureTheory.Measure

variable {α R : Type*} {mα : MeasurableSpace α}
  {μ μ₁ μ₂ ν ν' : Measure α} {s t : Set α}

theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.ge_iff_eq'

end MeasureTheory.Measure
end
end
