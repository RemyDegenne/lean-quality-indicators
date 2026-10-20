namespace P2MW.S_AutomorphicForm_isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace HChart

open Topology

open LanglandsTunnell.CubicInduction (diagUnits2)

section Diag

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def entries (g : GL (Fin 2) R) : (R × Rᵐᵒᵖ) × (R × Rᵐᵒᵖ) :=
  (((g : Matrix (Fin 2) (Fin 2) R) 0 0, MulOpposite.op (((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0)),
   ((g : Matrix (Fin 2) (Fin 2) R) 1 1, MulOpposite.op (((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1)))

end Diag
end HChart
end P2MW.S_AutomorphicForm_isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2
