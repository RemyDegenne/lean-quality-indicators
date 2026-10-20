namespace P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion

set_option autoImplicit false

noncomputable section

namespace A2FRS

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

open scoped MatrixGroups ModularForm Pointwise

section Groups

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

end Groups
end A2FRS
end
end P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
