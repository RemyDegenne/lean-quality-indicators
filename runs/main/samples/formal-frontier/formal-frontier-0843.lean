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

theorem weightOneValuation_eq_iff (S T : Set σ) (i : S) (j : T) :
    weightOneValuation (k := k) S i = weightOneValuation (k := k) T j ↔ S = T := by
  constructor
  · intro h
    ext a
    rw [← weightOneValuation_X_lt_one_iff (k := k) S i a,
      ← weightOneValuation_X_lt_one_iff (k := k) T j a, h]
  · intro h
    subst T
    exact weightOneValuation_pivot_eq S i j

end Field
end MvPolynomial
end
