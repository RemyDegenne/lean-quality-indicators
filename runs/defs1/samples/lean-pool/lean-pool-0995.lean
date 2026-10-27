@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The effective pole divisor containing the rectangular monomial grid
`x^i y^j` with `i ≤ n` and `j < b`. -/
def planeMonomialPoleBudget (x y : L) (n b : ℕ) :
    FiniteExtensionDivisor K L :=
  n • finiteExtensionPoleDivisor K L x +
    (b - 1) • finiteExtensionPoleDivisor K L y

end
end BGS.HasseWeil
end
