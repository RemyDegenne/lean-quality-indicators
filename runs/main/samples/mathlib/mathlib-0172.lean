public section

namespace NumberField

open Module NumberField NumberField.InfinitePlace Matrix

open scoped Real nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

open MeasureTheory MeasureTheory.Measure ZSpan NumberField.mixedEmbedding
  NumberField.InfinitePlace ENNReal NNReal Complex

section rootDiscr

theorem rootDiscr_def : rootDiscr K = |discr K| ^ (finrank ℚ K : ℝ)⁻¹ := by
  rw [rootDiscr]

end rootDiscr
end NumberField
end
