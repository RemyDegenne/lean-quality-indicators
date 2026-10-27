namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace R4SignProj

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

def liftGL : GL (Fin 3) ℝ →* G3 := (archInclN (Fin 3) ℚ).comp (Units.map rho.toMonoidHom)

end R4SignProj
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable
