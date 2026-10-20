@[expose] public section

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h

end Inv
end ENNReal
end
