namespace P2MW.S_AlgebraicCurve_RationalFunctionField_indexOfSpecialtyFinite_of_ratFunc_tower

attribute [-instance] AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option maxHeartbeats 3200000

open Polynomial

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Index

variable [IsCurveOver K F] [Nonempty (Place K F)]

theorem adeleBddSup_eq_of_degree_sub_ell_eq {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)]
    (heq : Divisor.degree D₂ - ell D₂ = Divisor.degree D₁ - ell D₁) :
    adeleBdd D₂ ⊔ globalSub K F = adeleBdd D₁ ⊔ globalSub K F := by
  obtain ⟨hfin, hdim⟩ := finrank_adeleBddSup_quotient hD
  rw [heq, sub_self] at hdim

  refine le_antisymm ?_ (sup_le_sup_right (adeleBdd_mono hD) _)
  haveI := hfin
  have hd0 : finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) = 0 := by
    exact_mod_cast hdim
  have hsub : Subsingleton (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) :=
    Module.finrank_zero_iff.mp hd0
  have htop := Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥(adeleBdd D₂ ⊔ globalSub K F)) ∈
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype := by
    rw [htop]; exact Submodule.mem_top
  exact hxc

end Index
end AlgebraicCurve
end
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_RationalFunctionField_indexOfSpecialtyFinite_of_ratFunc_tower
