namespace P2MW.S_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

noncomputable section

namespace A2FRH

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries AlgebraicCurve

open scoped MatrixGroups ModularForm Pointwise

section Rep

local notation "Qb" => AlgebraicClosure ℚ

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

include hT

theorem rep_mul {X Y : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL Γ) k₁}
    {f₂ g₂ : ModularForm (ΓGL Γ) k₂} (h₁ : X * qC g₁ = qC f₁) (h₂ : Y * qC g₂ = qC f₂) :
    (X * Y) * qC (⇑(g₁.mul g₂)) = qC (⇑(f₁.mul f₂)) := by
  rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul hT, qC_mul hT]
  linear_combination qC ⇑f₂ * h₁ + X * qC ⇑g₁ * h₂

end Rep
end A2FRH
end
end P2MW.S_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar
