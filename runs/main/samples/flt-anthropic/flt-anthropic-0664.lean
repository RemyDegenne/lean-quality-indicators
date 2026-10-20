namespace P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace TOLD0b

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Expand

variable {N : ℕ} {k : ℤ}

theorem qC_levelRaise (p : ℕ) [NeZero p] (f : ModularForm (Γ1 N) k) :
    qC (levelRaise p f) = qExpand ℂ p (qC f) := by
  rw [coe_levelRaise, qC, qExpansion_comp_heckeDiag, ofPowerSeries_expandPS, qC]

end Expand
end TOLD0b
end
end P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
