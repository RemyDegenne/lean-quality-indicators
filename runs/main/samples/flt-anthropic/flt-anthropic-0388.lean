namespace P2MW.S_CerednikDrinfeld_isAddCyclic_ker_iff_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise

open QuaternionAlgebra CerednikDrinfeld

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise

open QuaternionAlgebra CerednikDrinfeld

namespace Ws47

namespace DictIdx

open WeierstrassCurve Ws47.BGlue

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

variable {a b : ℚ}

p2m_reactivate

section Realised2

variable {q' : ℕ} [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
  {X₁ : WeierstrassCurve κ} [X₁.IsElliptic]
  {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} {θ₁ : ↥(rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b]}
  {x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
  {W : WeierstrassCurve κ} [W.IsElliptic] {χ : X₁.toAffine.Point →+ W.toAffine.Point} {d : (ℍ[ℚ, a, b])ˣ}
  {g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
  {W' : WeierstrassCurve κ} [W'.IsElliptic] {ψ : W.toAffine.Point →+ W'.toAffine.Point}
  {ψ' : W'.toAffine.Point →+ W.toAffine.Point}

namespace RFrame

variable (R : RFrame q' X₁ Λ₁ θ₁ x W χ d g W' ψ ψ')

include R

theorem hfg : (ratHom W X₁).FG := by
  rw [← AddGroup.fg_iff_addSubgroup_fg]
  haveI : Module.Finite ℤ ↥(Submodule.ofFiniteIdele Λ₁ x) := Module.Finite.iff_fg.mpr R.I_fg_span.1
  haveI : AddGroup.FG ↥(Submodule.ofFiniteIdele Λ₁ x) := Module.Finite.iff_addGroup_fg.mp inferInstance
  exact AddGroup.fg_of_surjective (f := R.ΦEquiv.symm.toAddMonoidHom) R.ΦEquiv.symm.surjective

end RFrame
end Realised2
end DictIdx
end Ws47
end P2MW.S_CerednikDrinfeld_isAddCyclic_ker_iff_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
