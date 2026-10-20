namespace P2MW.S_CerednikDrinfeld_natCard_ofFiniteIdele_primeHeckeSet_eq_natCard_subgroup_dualPair_ker_of_inf_conjByFiniteIdele

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise

p2m_open

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise

p2m_open

set_option autoImplicit false

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

namespace GOODEQ

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

theorem localBox_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q : ℕ}
    {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q) (v : HeightOneSpectrum (𝓞 ℚ))
    (hqv : algebraMap ℚ (v.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ) :
    Submodule.localBox (CerednikDrinfeld.meetOrder R n) v = Submodule.localBox R v := by
  apply le_antisymm (HeckeLocal.localBox_mono inf_le_left v)
  unfold Submodule.localBox
  rw [AddSubgroup.closure_le]
  rintro _ ⟨z, hz, c, hc, rfl⟩
  have hq0 : (q : ℚ) ≠ 0 := by
    rintro h
    have : q = 0 := by exact_mod_cast h
    subst this
    exact hn.2.2.2 (by rw [Nat.cast_zero, inv_zero, zero_smul]; exact zero_mem _)

  have e : z ⊗ₜ[ℚ] c = ((q : ℤ) • z) ⊗ₜ[ℚ] (algebraMap ℚ (v.adicCompletion ℚ) ((q : ℚ)⁻¹) * c) := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, TensorProduct.smul_tmul, Algebra.smul_def, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hq0, map_one, one_mul]
  rw [e]
  exact AddSubgroup.subset_closure ⟨_, natCast_smul_mem_meetOrder hR hn hz, _, mul_mem hqv hc, rfl⟩

end GOODEQ
end P2MW.S_CerednikDrinfeld_natCard_ofFiniteIdele_primeHeckeSet_eq_natCard_subgroup_dualPair_ker_of_inf_conjByFiniteIdele
