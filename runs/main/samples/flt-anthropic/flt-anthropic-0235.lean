namespace P2MW.S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar

open IsDedekindDomain AutomorphicForm AdelicDock

open scoped ComplexConjugate TensorProduct TensorProduct.RightActions NumberField.PlaceTransport Pointwise

namespace R4ResSigma

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Analytic

theorem lambdaT_eq_ite {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G] (μ : Measure Q) [IsProbabilityMeasure μ]
    (u : Q → G) (H : G → ℝ) (T : ℝ) (φ : G → ℂ) (hφ : ∀ q g, φ (u q * g) = φ g) (g : G) :
    lambdaT μ u H T φ g = if H g ≤ T then φ g else 0 := by
  have hct : constantTerm μ u φ g = φ g := by
    simp [constantTerm, constantTermIntegrand, hφ]
  by_cases hg : H g ≤ T
  · rw [if_pos hg, lambdaT_apply_of_le _ _ hg]
  · rw [if_neg hg, lambdaT_apply_of_lt _ _ (lt_of_not_ge hg), hct, sub_self]

end Analytic
end R4ResSigma
end
end P2MW.S_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv
