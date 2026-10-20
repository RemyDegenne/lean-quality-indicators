universe u

open IGame

@[expose] public noncomputable section

namespace Real

@[simp] theorem toSurreal_neg_iff {x : ℝ} : (x : Surreal) < 0 ↔ x < 0 := by norm_cast

end Real
end
