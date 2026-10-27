namespace P2MW.S_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace ParInt

open scoped MatrixGroups

open ModularCurve.Period

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

abbrev A : Type := Additive (Abelianization ↥Γ)

end ParInt
end P2MW.S_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
