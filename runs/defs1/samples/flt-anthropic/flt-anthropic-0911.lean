namespace P2MW.S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward

attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace WeierstrassCurve p2m_export "WeierstrassCurve" "Affine isUnit_Δ a₃ map_map a₁ Affine.map_a₃ map Affine.CoordinateRing mk a₄ a₂ a₆ Affine.map_a₆ IsIntegral toAffine Affine.map_a₂ Affine.Point Affine.map_a₁ Affine.map_a₄ map_Δ map_a₆ map_a₁ map_a₄ Δ Affine.equation_iff Affine.polynomial map_a₂ baseChange j map_a₃ Affine.IsogenyEndDatum Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred Affine.CoordinateRing.isDedekindDomain Affine.hasPrincipalDivisors_functionField Affine.GenusOnePlaceGate.ext_of_isCentred Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom" namespace Affine p2m_export "WeierstrassCurve.Affine" "Point.add Equation CoordinateRing.basis_one equation_iff' map_a₃ slope CoordinateRing map baseChange Equation.baseChange Nonsingular map_a₆ FunctionField map_a₂ Point CoordinateRing.mk addX map_a₁ CoordinateRing.map map_a₄ CoordinateRing.basis_apply CoordinateRing.map_mk CoordinateRing.exists_smul_basis_eq CoordinateRing.map_smul CoordinateRing.basis_zero equation_iff_nonsingular CoordinateRing.basis addY equation_iff polynomial pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint pointClass AbelTheorem genusOnePic0Equiv GenusOnePlaceGate.deg_eq_one GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot hasPrincipalDivisors_functionField natCard_ker_pointMapOfPushforward_eq_finrankAlong polyToFunctionField polyToFunctionField_apply polyToFunctionField_injective polyToFunctionField_C algebraMap_smul_basis algebraMap_polynomial_eq_polyToFunctionField yCoord isIntegral_yCoord exists_genusOnePlaceGate_isCentred_and_abelTheorem GenusOnePlaceGate.ext_of_isCentred isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom" end WeierstrassCurve.Affine

p2m_open_scoped "WeierstrassCurve WeierstrassCurve.Affine" in

scoped instance WeierstrassCurve.Affine.instHasPrincipalDivisorsFunctionField_s13e2
    {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve.Affine F) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField W

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable scoped instance (priority := 50) s13DecEqAlgebraicClosure {K₀ : Type*} [Field K₀] :
    DecidableEq (AlgebraicClosure K₀) := Classical.decEq _

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

universe uK

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

section

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 3200000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

noncomputable section

namespace ModularCurve

p2m_open

section BCCanonical

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

variable (E E' : WeierstrassCurve K) [E.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E] [WeierstrassCurve.Affine.AbelTheorem E] [E'.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate E'] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred E'] [WeierstrassCurve.Affine.AbelTheorem E']

variable (ι : E'.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)

def kw_surgehgf4_hSD_genSet : Set K :=
  ({E.a₁, E.a₂, E.a₃, E.a₄, E.a₆} : Set K) ∪ {E'.a₁, E'.a₂, E'.a₃, E'.a₄, E'.a₆} ∪
    ↑(kw_iCa_ffCoeffSet E (ι (polyToFunctionField E'.toAffine Polynomial.X))) ∪
    ↑(kw_iCa_ffCoeffSet E (ι (yGen E'.toAffine)))

end BCCanonical
end ModularCurve
end
end
end
end WeierstrassCurve
end
end P2MW.S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
