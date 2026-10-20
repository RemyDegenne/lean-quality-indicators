namespace P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise

p2m_open

noncomputable section

namespace CerednikDrinfeld

namespace BrandtLevel

p2m_open

section Frame

open WeierstrassCurve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

variable {a b : ℚ}

variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]} {χ : Pt κ X₀ →+ Pt κ W}
  {d : (ℍ[ℚ, a, b])ˣ} {x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

theorem mem_modOf_iff (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) {χ : Pt κ X₀ →+ Pt κ W}
    (hχ : χ ∈ rationalHomSet κ X₀ W) (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) (ρ : Pt κ W →+ Pt κ X₀) :
    ρ ∈ modOf θ hχ d J ↔ ∃ h : ρ ∈ rationalHomSet κ W X₀, tr θ hχ d ⟨ρ, h⟩ ∈ J := by
  unfold modOf
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨ρ', hρ', rfl⟩
    exact ⟨ρ'.2, hρ'⟩
  · rintro ⟨h, hJ⟩
    exact ⟨⟨ρ, h⟩, hJ, rfl⟩

end Frame
end BrandtLevel
end CerednikDrinfeld
end
end P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker
