namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set

open scoped Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter Function Set

open scoped Topology NNReal

open MeasureTheory ProbabilityTheory Filter Function Set

open scoped Topology NNReal

open MeasureTheory ProbabilityTheory Filter Function Set

open scoped Topology NNReal

open MeasureTheory ProbabilityTheory Filter Function Set

open scoped Topology NNReal

namespace ParisiFinite

lemma sineWeight_bound (L : ℝ≥0) (hL : 0<L) (x : ℝ) :
    |(sineWeight L hL).val x|≤L := by
  change |(L:ℝ)*Real.sin (x/L)|≤L
  rw [abs_mul,abs_of_nonneg L.coe_nonneg]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) L.coe_nonneg

end ParisiFinite
end
end OAI
