namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors ENNReal NNReal

open NumberField.AdelicLevel (diagOne)

noncomputable section

namespace E3ReduceSupplyF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ

theorem level_zero_inv :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x ≠ 1 := by
  obtain ⟨h0, h1⟩ := level_zero p
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [AddChar.inv_apply]; exact h0 (-x) (by rwa [Valuation.map_neg])
  · obtain ⟨x, hx, hne⟩ := h1
    refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
    rwa [AddChar.inv_apply, neg_neg]

end E3ReduceSupplyF
end
end P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal
