namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open NumberField.AdelicLevel (diagOne)

open scoped Classical

open scoped NNReal ENNReal Topology

noncomputable section

namespace SVDGlue

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem continuous_det : Continuous fun h : G₂ => (Matrix.GeneralLinearGroup.det h : Fˣ) := by
  refine Units.continuous_iff.mpr ⟨continuous_val_det p, ?_⟩
  have : (fun h : G₂ => (((Matrix.GeneralLinearGroup.det h)⁻¹ : Fˣ) : F)) = fun h => (((h⁻¹ : G₂) : M2)).det := by
    funext h
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Units.continuous_coe_inv.matrix_det

end SVDGlue
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
