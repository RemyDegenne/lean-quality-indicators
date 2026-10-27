namespace P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

p2m_open

open scoped MatrixGroups ModularForm Pointwise

namespace ES1Sol

local notation "Qb" => AlgebraicClosure ℚ

section Diamond

variable {M : ℕ}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

end Diamond
end ES1Sol
end
end P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat
