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

/-- The pullback of the `X`-adic valuation along the birational coordinates. -/
noncomputable def weightOneValuation : Valuation K ℤᵐ⁰ :=
  ((Polynomial.idealX Cw).valuation (RatFunc Cw)).comap
    (weightOneCoordinates S i).toRingHom

end Field
end MvPolynomial
end
