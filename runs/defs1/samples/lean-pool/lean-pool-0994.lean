@[expose] public section

namespace BollobasNikiforov

open Matrix

open scoped Matrix

noncomputable section

variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)

/-- Scalar `Δ = det 𝒜`. -/
def Δ : ℝ :=
  (𝒜 t q).det

end
end BollobasNikiforov
end
