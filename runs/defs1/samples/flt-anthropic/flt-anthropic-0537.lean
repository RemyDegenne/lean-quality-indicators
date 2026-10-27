set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

set_option linter.unusedVariables false in
set_option linter.unusedVariables false in

def IsCuspidal' (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ a : A, W.ord (jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
    (a : AlgebraicClosure ℚ)) ≤ 0

end PlaceSpecialization
end ModularCurve
end
