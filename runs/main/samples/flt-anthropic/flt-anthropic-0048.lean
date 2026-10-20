namespace P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar

attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

open scoped MatrixGroups ModularForm Classical

open IntermediateField AlgebraicCurve ModularCurve

namespace PLCDSol

section Modular

open ModularForm UpperHalfPlane

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "Qb" => AlgebraicClosure ℚ

local notation "ΓH" => CohCarrier.GammaH M H

scoped instance instFiniteIndexGammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem exists_gamma0_apply_eq (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  refine ⟨γ.1, γ.2, ?_⟩
  have h : ((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) = d := by rw [hγ, inv_inv]
  have h2 : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = ((γ.1 0 0 : ℤ) : ZMod M) := rfl
  rw [← h2, h]

end Modular
end PLCDSol
end
end P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar
