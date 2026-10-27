@[expose] public section

namespace Stafford38.PolynomialOperatorTaylorProjection

open scoped BigOperators

open Stafford38.PolynomialDifferentialOperators

open Stafford38.PolynomialOperatorCommutators

noncomputable section

variable (k : Type*) [Field k] [CharZero k] (n : ℕ)

/-- The polynomial coefficient algebra for the finite Taylor projection. -/
abbrev PolynomialRing := MvPolynomial (Fin n) k

end
end Stafford38.PolynomialOperatorTaylorProjection
end
