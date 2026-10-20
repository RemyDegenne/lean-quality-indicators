@[expose] public section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

section Shift

variable {alpha : Type*} [PseudoMetricSpace alpha]

theorem coe_add_lt_exitTime_iff (U : Set alpha) (omega : ContinuousPath alpha) (t s : NNReal) :
    ((t + s : NNReal) : ℝ≥0∞) < exitTime U omega ↔
      (t : ℝ≥0∞) < exitTime U omega ∧ (s : ℝ≥0∞) < exitTime U (shift t omega) := by
  constructor
  · intro h
    have ht : (t : ℝ≥0∞) < exitTime U omega :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.mpr le_self_add) h
    refine ⟨ht, ?_⟩
    rw [← exitTime_shift_add U omega t ht, ENNReal.coe_add, add_comm] at h
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).mp h
  · rintro ⟨ht, hs⟩
    rw [← exitTime_shift_add U omega t ht, ENNReal.coe_add, add_comm]
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).mpr hs

end Shift
end MarkovProcess.ContinuousPath
end
