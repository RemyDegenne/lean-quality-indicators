namespace P2MW.S_ModularCurve_two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero

attribute [-instance] ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise

open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

namespace HwCurve

open ModularCurve AlgebraicCurve WeierstrassCurve

section Units

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  (W : WeierstrassCurve κ) [W.IsElliptic]

noncomputable def stabEquiv (C : AddSubgroup (Pt W)) :
    {ι : Pt W →+ Pt W // ι ∈ rationalHomSet κ W W ∧
        (∃ ι' ∈ rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C.map ι = C} ≃ MulAction.stabilizer (G W) C where
  toFun ι := ⟨unitOf W ι.1 ι.2.2.1.choose ι.2.1 ι.2.2.1.choose_spec.1 ι.2.2.1.choose_spec.2.1
      ι.2.2.1.choose_spec.2.2, by
        rw [MulAction.mem_stabilizer_iff, smul_eq_map, toHom_unitOf]; exact ι.2.2.2⟩
  invFun g := ⟨toHom W g, toHom_mem W _, ⟨toHom W g⁻¹, toHom_mem W _, toHom_inv_comp W _, toHom_comp_inv W _⟩, by
      rw [← smul_eq_map]; exact g.2⟩
  left_inv ι := Subtype.ext rfl
  right_inv g := Subtype.ext (Units.ext (Subtype.ext rfl))

end Units
end HwCurve
end P2MW.S_ModularCurve_two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace
