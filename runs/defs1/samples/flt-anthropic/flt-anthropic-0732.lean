namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Matrix MeasureTheory Topology Filter TopologicalSpace

namespace LanglandsTunnell

namespace CubicInduction

namespace ArchConvCalculus

p2m_open

def omega3 (β : E33 → ℂ) : E33 → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, leftDeriv i j (leftDeriv j k (leftDeriv k i β)) m

end ArchConvCalculus
end CubicInduction
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart
