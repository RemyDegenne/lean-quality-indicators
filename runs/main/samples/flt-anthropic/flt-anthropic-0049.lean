namespace P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one

attribute [-instance] ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors

attribute [-instance] AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open scoped MatrixGroups

namespace CohCarrier

p2m_open

open CongruenceSubgroup

open scoped MatrixGroups

theorem gammaH_inf_gamma0_mul (N ℓ : ℕ) [NeZero N] [NeZero (N * ℓ)] (H' : Subgroup (ZMod N)ˣ) :
    CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ) =
      CohCarrier.GammaH (N * ℓ) (H'.comap (ZMod.unitsMap (dvd_mul_right N ℓ))) := by
  ext γ
  have hcast : ∀ z : ℤ, ZMod.castHom (dvd_mul_right N ℓ) (ZMod N) ((z : ZMod (N * ℓ))) = (z : ZMod N) :=
    fun z => map_intCast _ z
  constructor
  · rintro ⟨hH, h0⟩
    obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hH
    refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
    rw [Subgroup.mem_comap]
    convert hd using 1
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ZMod.unitsMap_def, hcast]
  · intro h
    obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp h
    rw [Subgroup.mem_comap] at hd
    have hγ0N : γ ∈ Gamma0 N := by
      rw [Gamma0_mem] at hγ0 ⊢
      have := congrArg (ZMod.castHom (dvd_mul_right N ℓ) (ZMod N)) hγ0
      rwa [hcast, map_zero] at this
    refine ⟨CohCarrier.mem_GammaH_iff.mpr ⟨hγ0N, ?_⟩, hγ0⟩
    convert hd using 1
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ZMod.unitsMap_def, hcast]

end CohCarrier
end P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one
