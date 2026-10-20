namespace P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion

set_option autoImplicit false

noncomputable section

namespace A2FRS

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

open scoped MatrixGroups ModularForm Pointwise

section Span

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def qExpSubmodule (M : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ) : Submodule ℂ (PowerSeries ℂ) where
  carrier := {P | ∃ f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k, qExpansion 1 ⇑f = P}
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f + g, ?_⟩
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos
      (one_mem_strictPeriods_of_T_mem (translation_mem_GammaH M H))]
  zero_mem' := ⟨0, by rw [ModularForm.coe_zero, qExpansion_zero]⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    refine ⟨c • f, ?_⟩
    rw [coe_smul_form, ModularForm.qExpansion_smul one_pos
      (one_mem_strictPeriods_of_T_mem (translation_mem_GammaH M H))]

end Span
end A2FRS
end
end P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
