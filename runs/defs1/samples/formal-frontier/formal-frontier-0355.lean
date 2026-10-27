@[expose] public section

open scoped WithZero

universe u v

namespace MvPolynomial

variable {σ : Type v}

/-- The unweighted variables and the ratios of weighted variables to a chosen pivot. -/
abbrev WeightOneCoefficientVariables (S : Set σ) (i : S) :=
  {j : σ // j ∉ S} ⊕ {j : σ // j ∈ S ∧ j ≠ (i : σ)}

end MvPolynomial
end
