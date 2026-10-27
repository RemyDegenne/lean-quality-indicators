@[expose] public section

open scoped BigOperators ContDiff

open MeasureTheory Real

open scoped Matrix

noncomputable
section

namespace NashEmbedding

variable {n : ℕ}

/-- `χ(x) = ψ_β(M x)`. -/
def rotBump (n : ℕ) (β : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  prodBump n β (M.mulVec x)

end NashEmbedding
end
end
