namespace P2MW.S_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

noncomputable section

open ModularCurve AlgebraicCurve IntermediateField HahnSeries CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

local notation "Qbar" => AlgebraicClosure ℚ

namespace X1FrickeG

section Defs

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [NeZero ℓ]

def IsDiaG (d : (ZMod M)ˣ) (σ : FB Γ ≃ₐ[Qbar] FB Γ) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ F0 Γ ∧
        ((σ ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
            FB Γ) : LaurentSeries Qbar) = coeffEmb Qbar y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

end Defs
end X1FrickeG
end
end P2MW.S_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul
