@[expose] public noncomputable section

open MeasureTheory

open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Interval-average-exceeds measurability obligation for every coordinate slice family. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n, SourceLocalizedMaximalAverageExceedsMeasurable (μslice i) t

end AleksandrovDifferentiability
end
