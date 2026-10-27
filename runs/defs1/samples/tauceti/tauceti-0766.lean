public section

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Universal.Jacobian

open WeierstrassCurve.Jacobian

variable {m n : ℤ}

/-- The three families of division polynomials as elements of the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n

end WeierstrassCurve.Universal.Jacobian
end
end
