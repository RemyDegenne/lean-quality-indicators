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

/-- Constant rational functions in the coefficient field lift to the valuation subring. -/
noncomputable def weightOneCoefficientSection :
    Cw →+* Vw := by
  refine ((weightOneCoordinates S i).symm.toRingHom.comp
    (RatFunc.C : Cw →+* RatFunc Cw)).codRestrict Vw ?_
  intro a
  change weightOneValuation (k := k) S i
    ((weightOneCoordinates S i).symm (RatFunc.C a)) ≤ 1
  rw [weightOneValuation_apply, RingEquiv.apply_symm_apply]
  change (Polynomial.idealX Cw).valuation (RatFunc Cw)
    (algebraMap (Polynomial Cw) (RatFunc Cw) (Polynomial.C a)) ≤ 1
  exact (Polynomial.idealX Cw).valuation_le_one (Polynomial.C a)

end Field
end MvPolynomial
end
