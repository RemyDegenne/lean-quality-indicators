namespace P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace TOLD0b

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Groups

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

end Groups
end TOLD0b
end
end P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
