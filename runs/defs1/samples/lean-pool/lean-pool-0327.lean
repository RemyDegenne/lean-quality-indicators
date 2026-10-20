@[expose] public section

open scoped BigOperators

open scoped ComplexConjugate

namespace BeyondBethe

/-- The real squarefree monomial selected by the true coordinates of a Boolean vector. -/
noncomputable def boolMonomial {n : ℕ}
    (x : Fin n → ℝ) (S : Fin n → Bool) : ℝ :=
  ∏ i, (x i) ^ (bif S i then (1 : ℕ) else 0)

end BeyondBethe
end
