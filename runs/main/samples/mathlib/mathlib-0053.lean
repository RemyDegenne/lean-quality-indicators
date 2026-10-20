@[expose] public section

noncomputable section

open Real NNReal ENNReal ComplexConjugate Finset Function Set

namespace NNReal

variable {x : ℝ≥0} {w y z : ℝ}

theorem one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow h h₁

end NNReal
end
end
