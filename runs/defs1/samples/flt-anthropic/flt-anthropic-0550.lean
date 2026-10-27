namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped ENNReal Classical

namespace P4mg

open NumberField

variable (K : Type) [Field K] [NumberField K]

noncomputable def mroot (n : ℕ) (p : mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  (fun w => (p.1 w) ^ ((n : ℝ)⁻¹), fun w => (p.2 w) ^ ((n : ℂ)⁻¹))

end P4mg
end P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_apply_norm_eq_integral_ker_norm_prod_of_contDiff
