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

section Unique

variable (Γ : Subgroup SL(2, ℤ))

variable {Γ}

theorem algHom_ext_gen {R : Type*} [Field R] [Algebra Qbar R] (φ ψ : FB Γ →ₐ[Qbar] R)
    (h : ∀ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      φ ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ =
        ψ ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩) :
    φ = ψ := by
  refine IntermediateField.algHom_ext_of_eq_adjoin Qbar (FB_eq_adjoin Γ) ?_
  rintro _ ⟨x, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
  exact h k f g pf pg hf hg hg0

end Unique
end X1FrickeG
end
end P2MW.S_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul
