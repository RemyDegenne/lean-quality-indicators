@[expose] public section

open scoped WithZero

universe u v

namespace MvPolynomial

variable {σ : Type v}

section Field

variable {k : Type u} [Field k] (S : Set σ) (i : S)

local notation "P" => MvPolynomial σ k

local notation "K" => FractionRing P

local notation "Cw" => WeightOneCoefficientField k S i

local notation "Aw" => MvPolynomial (WeightOneCoefficientVariables S i) k

/-- The coefficient of the lowest-weight term in the univariate expansion. -/
noncomputable def weightOneInitial (p : P) : Cw :=
  (weightOneExpansion S i p).coeff (weightOneNatOrder S p)

end Field
end MvPolynomial
end
