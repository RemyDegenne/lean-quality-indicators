namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option synthInstance.maxSize 8192

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped TensorProduct TensorProduct.RightActions

open scoped Classical

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace LayerPlumbing

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isOpen_setOf_isUnit_mixedSpace : IsOpen {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x} := by
  have h : {x : NumberField.mixedEmbedding.mixedSpace L | IsUnit x} =
      (⋂ w, {x | x.1 w ≠ 0}) ∩ (⋂ w, {x | x.2 w ≠ 0}) := by
    ext x; simp [isUnit_mixedSpace_iff]
  rw [h]
  refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_iInter_of_finite fun w => ?_)
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const

end LayerPlumbing
end
end P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex
