namespace P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option Elab.async false

p2m_reactivate

p2m_reactivate

namespace UqNSol

open scoped Pointwise

open AlgebraicCurve AlgebraicCurve.SemilinearAut ModularCurve ModularCurve.PlaceSpecialization

local notation "Qb" => AlgebraicClosure ℚ

section L2

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [hqN : Fact (¬ q ∣ N)] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

local notation "α₁" => heckeAlphaBar (AlgebraicClosure ℚ) N q

local notation "β₁" => heckeBetaBar (AlgebraicClosure ℚ) N q

local notation "wF" => geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)

local notation "φg" => frobOnPlacesGeomLevel k N data hKr

local notation "Dv" => Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))

local notation "Pl" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))

theorem fstDiv_sum (P : PlaceSpecialization A q N data hKr k red hα hβ) {ι : Type*} (s : Finset ι) (f : ι → Dv) :
    P.fstDiv (∑ i ∈ s, f i) = ∑ i ∈ s, P.fstDiv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold PlaceSpecialization.fstDiv
    exact Finsupp.filter_zero _
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fstDiv_add, ih]

end L2
end UqNSol
end P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible
