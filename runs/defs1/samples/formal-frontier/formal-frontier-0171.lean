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

local notation "Vw" => Valuation.valuationSubring (weightOneValuation (k := k) S i)

/-- The pivot, viewed as an element of the valuation subring. -/
noncomputable def weightOneUniformizer : Vw :=
  ⟨algebraMap P K (X (i : σ)), weightOneValuation_pivot_mem S i⟩

end Field
end MvPolynomial
end
