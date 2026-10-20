namespace P2MW.S_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

noncomputable section

open ModularCurve AlgebraicCurve IntermediateField HahnSeries CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

local notation "Qbar" => AlgebraicClosure ℚ

namespace X1FrickeG

section Transport

variable (M : ℕ) [NeZero M]

theorem exists_frLaws_one : ∃ w, FrLawsG M (Gamma1 M) w := by
  have key : ∀ Γ : Subgroup SL(2, ℤ), Γ = CohCarrier.GammaH M ⊥ → ∃ w, FrLawsG M Γ w := by
    rintro Γ rfl
    exact exists_frLaws_bot M
  exact key _ (GammaH_bot M).symm

end Transport
end X1FrickeG
end
end P2MW.S_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul
