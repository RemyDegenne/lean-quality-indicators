namespace P2MW.S_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix

open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory Filter Topology

namespace TraceKernel

namespace RowUnit

variable {M : Matrix (Fin 2) (Fin 2) ℂ}

theorem norm_sq_le_one (h : RowUnit M) (i j : Fin 2) : ‖M i j‖ ^ 2 ≤ 1 := by
  have hi := h i
  have h0 := sq_nonneg ‖M i 0‖
  have h1 := sq_nonneg ‖M i 1‖
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · linarith
  · linarith

end RowUnit
end TraceKernel
end P2MW.S_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt
