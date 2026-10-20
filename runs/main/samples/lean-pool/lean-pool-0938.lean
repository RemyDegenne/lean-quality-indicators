@[expose] public noncomputable section

open MeasureTheory MeasureTheory.Measure Set

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical in
theorem radial_slice_smul (i : ι) (t : ℝ) (v : {j : ι // j ≠ i} → ℝ) :
    (Homeomorph.funSplitAt ℝ i).symm (t - ∑ j, t * v j, t • v) =
      t • stdSimplexCoordMap i v := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [stdSimplexCoordMap, ← Finset.mul_sum, mul_sub]
  · simp [stdSimplexCoordMap, hj]

end MeasureTheory
end
