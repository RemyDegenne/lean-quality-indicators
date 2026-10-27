@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex Polynomial

open scoped Real Manifold MatrixGroups

/-- The diagonal polynomial `G_m(X) := Φ_m(X, X) ∈ ℚ[X]`, obtained by substituting the outer
variable `X` for the coefficient variable `Y` (the `ℚ`-analogue of `diagPhiZ`). -/
def diagPhiQ (PhiQ : Polynomial (Polynomial ℚ)) : Polynomial ℚ :=
  PhiQ.eval (X : Polynomial ℚ)

end Chudnovsky
end
end
