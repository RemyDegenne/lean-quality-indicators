open scoped HahnSeries

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable (H : AddSubgroup ℝ) {K : Type v} [Field K]

@[simp]
theorem realSupportSup_one :
    realSupportSup H (1 : Nonpositive H K) = 0 := by
  rw [realSupportSup, map_one]
  rw [show (1 : Nonpositive ℝ K) = single 0 1 le_rfl by
    apply Subtype.ext
    rw [coe_single]
    rfl]
  exact supportSup_single one_ne_zero le_rfl

end HahnSeries.Nonpositive
end
