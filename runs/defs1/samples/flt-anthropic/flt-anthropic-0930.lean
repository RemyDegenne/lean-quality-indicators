namespace P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane hiding I

open ModularCurve HahnSeries CongruenceSubgroup WeierstrassCurve WeierstrassCurve.Affine

open scoped MatrixGroups ModularForm

namespace R4TateModelK

section Groups

variable (N M' : ℕ) [NeZero N] [NeZero M']

abbrev Γgl : Subgroup (GL (Fin 2) ℝ) := (Γsl N M' : Subgroup (GL (Fin 2) ℝ))

end Groups
end R4TateModelK
end
end P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level
