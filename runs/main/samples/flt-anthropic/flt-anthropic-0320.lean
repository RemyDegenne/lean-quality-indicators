namespace P2MW.S_ModularCurve_ord_sub_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer_fullKernelQuotient

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.Gamma0Pair.isElliptic ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk

set_option autoImplicit false

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_open

open scoped IntermediateField Pointwise

p2m_open

open scoped IntermediateField

universe u v

namespace ORDJN

theorem finiteDimensional_adjoin_of_transcendental {K M : Type*} [Field K] [Field M] [Algebra K M]
    (t : M) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ M] (t' : M) (ht' : Transcendental K t') :
    FiniteDimensional K⟮t'⟯ M := by

  haveI : Algebra.IsAlgebraic K⟮t⟯ M := Algebra.IsAlgebraic.of_finite K⟮t⟯ M
  haveI halg : Algebra.IsAlgebraic K⟮t'⟯ M := AlgebraicCurve.isAlgebraic_adjoin_of_transcendental t ht'

  let E : IntermediateField K⟮t'⟯ M := IntermediateField.adjoin K⟮t'⟯ {t}
  haveI hEfin : FiniteDimensional K⟮t'⟯ E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K⟮t'⟯) t)

  have hle : K⟮t⟯ ≤ E.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact IntermediateField.mem_adjoin_simple_self K⟮t'⟯ t
  letI : Algebra K⟮t⟯ E := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K⟮t⟯ E M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Module.Finite E M := Module.Finite.of_restrictScalars_finite K⟮t⟯ E M
  exact Module.Finite.trans E M

end ORDJN
end P2MW.S_ModularCurve_ord_sub_mul_natCard_stabilizer_zmultiples_reduceHom_eq_ramificationIndexAlong_mul_natCard_stabilizer_fullKernelQuotient
