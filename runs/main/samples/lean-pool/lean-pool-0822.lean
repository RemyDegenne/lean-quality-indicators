@[expose] public section

namespace Sendov

namespace Batch40To41

lemma c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 40 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]

end Batch40To41
end Sendov
end
