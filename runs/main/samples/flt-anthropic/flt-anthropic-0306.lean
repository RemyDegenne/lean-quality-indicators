namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer

attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

noncomputable section

p2m_open

open scoped MatrixGroups Topology Manifold

open MulAction

open scoped MatrixGroups

namespace ModularCurve

namespace ComplexPlaceDictionaryOf

namespace RamEqCard

p2m_open

scoped instance normal_zpowers_neg_one : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun a ha g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hc : g * (-1 : SL(2, ℤ)) ^ k * g⁻¹ = (-1) ^ k := by
    rw [((Commute.neg_one_right g).zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hc]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

scoped instance (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (pm Γ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pm Γ)

scoped instance finite_stabilizer_SL (σ : ℍ) : Finite (MulAction.stabilizer SL(2, ℤ) σ) := by
  have hfin := ProperlyDiscontinuousSMul.finite_stabilizer (Γ := 𝒮ℒ) σ
  have : Finite (MulAction.stabilizer (𝒮ℒ) σ) := hfin
  refine Finite.of_injective
    (fun γ => (⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)), ⟨γ, rfl⟩⟩, γ.2⟩ :
      MulAction.stabilizer (𝒮ℒ) σ)) ?_
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer (𝒮ℒ) σ => ((x : 𝒮ℒ) : GL (Fin 2) ℝ)) h
  exact Subtype.ext (Matrix.SpecialLinearGroup.mapGL_injective this)

scoped instance finite_stabilizer_sub (Γ' : Subgroup SL(2, ℤ)) (σ : ℍ) :
    Finite (MulAction.stabilizer Γ' σ) := by
  refine Finite.of_injective
    (fun γ => (⟨((γ : Γ') : SL(2, ℤ)), γ.2⟩ : MulAction.stabilizer SL(2, ℤ) σ)) ?_
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer SL(2, ℤ) σ => (x : SL(2, ℤ))) h
  exact Subtype.ext (Subtype.ext this)

variable {Γ : Subgroup SL(2, ℤ)} {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

section Orbits

variable (Γ)

variable {Γ}

theorem two_mul_card_div_two (σ : ℍ) :
    (2 : ℤ) * ((Nat.card (MulAction.stabilizer SL(2, ℤ) σ) / 2 : ℕ) : ℤ) =
      (Nat.card (MulAction.stabilizer SL(2, ℤ) σ) : ℤ) := by
  obtain ⟨m, hm⟩ := two_dvd_card_stabilizer σ
  rw [hm, Nat.mul_div_cancel_left _ two_pos]
  push_cast
  ring

end Orbits
end RamEqCard
end ComplexPlaceDictionaryOf
end ModularCurve
end
end P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer
