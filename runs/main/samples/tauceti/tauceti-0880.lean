public section

namespace TauCeti

open Complex Metric Set

open scoped ComplexConjugate

@[simp]
lemma pseudoHyperbolicExpr_zero_right (z : ℂ) : pseudoHyperbolicExpr z 0 = ‖z‖ := by
  simp [pseudoHyperbolicExpr]

end TauCeti
end
