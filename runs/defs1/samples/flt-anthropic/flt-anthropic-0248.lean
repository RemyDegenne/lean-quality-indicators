namespace P2MW.S_CohCarrier_exists_perfectPairing_antisymm_cornerSubmodule_H1_of_not_isEisenstein

attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace CohCarrier

namespace CornerDual

p2m_open

section Integral

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)

open ModularCurve.CupPairing ModularCurve.PDPairing ModularCurve.Period

def rat {Γ : Subgroup SL(2, ℤ)} (φ : Additive Γ →+ ℤ) : Additive Γ →+ ℚ := (Int.castAddHom ℚ).comp φ

end Integral
end CornerDual
end CohCarrier
end P2MW.S_CohCarrier_exists_perfectPairing_antisymm_cornerSubmodule_H1_of_not_isEisenstein
