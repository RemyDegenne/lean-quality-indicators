public section

variable {E : Type*}

open Filter

open ENNReal Filter NNReal

namespace Real

variable {r : ℝ}

lemma enorm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ := by
  simp [Real.enorm_of_nonneg, ha]

end Real
end
