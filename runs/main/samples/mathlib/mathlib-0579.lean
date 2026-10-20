@[expose] public section

noncomputable section

open Real Finset Set

namespace Real

variable {x y z : ℝ} {n : ℕ}

lemma monotone_rpow_of_base_ge_one {b : ℝ} (hb : 1 ≤ b) :
    Monotone (b ^ · : ℝ → ℝ) := by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp

end Real
end
end
