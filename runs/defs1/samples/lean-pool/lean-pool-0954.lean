@[expose] public section

namespace BollobasNikiforov

open Matrix

open scoped Matrix

noncomputable section

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

/-- Scalar `a₀ = 1 + m₀`. -/
def a0 : ℝ :=
  1 + m t q 0

end
end BollobasNikiforov
end
