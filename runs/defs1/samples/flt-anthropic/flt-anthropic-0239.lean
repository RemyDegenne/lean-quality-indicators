namespace P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace R1CuspDeriv

open MeasureTheory Filter Metric Topology

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

section Arch

def U : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

end Arch
end R1CuspDeriv
end
end P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
