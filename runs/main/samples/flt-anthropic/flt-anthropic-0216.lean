namespace P2MW.S_AutomorphicForm_exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace R1EdCellSplit

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

open NumberField.AdelicHeight IsDedekindDomain

open AutomorphicForm AutomorphicForm.WindowedSiegel

open scoped Topology

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] isAddHaar

section HeightLocal

variable {k : Type*} [NormedField k]

theorem bottom_row_mul {s : GL (Fin 2) k} (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    (g : GL (Fin 2) k) (j : Fin 2) :
    ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 j
      = (s : Matrix (Fin 2) (Fin 2) k) 1 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 j := by
  rw [coe_mul', Matrix.mul_apply, Fin.sum_univ_two, h10]
  ring

end HeightLocal
end R1EdCellSplit
end
end P2MW.S_AutomorphicForm_exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell
