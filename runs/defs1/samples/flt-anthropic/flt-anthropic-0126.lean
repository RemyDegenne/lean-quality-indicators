namespace P2MW.S_ModPForms_finiteDimensional_modPMod

set_option autoImplicit false

open UpperHalfPlane

open scoped MatrixGroups

p2m_reactivate

namespace RedRank

section Lattice

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)

local notation "MF" => ModularForm Γ₀(N) k

def latt (W : Submodule ℂ MF) : Submodule ℤ MF where
  carrier := {v | v ∈ W ∧ ∀ n, ∃ m : ℤ, ModularFormClass.qCoeff (⇑v) n = m}
  add_mem' {v w} hv hw := ⟨W.add_mem hv.1 hw.1, fun n => by
    obtain ⟨a, ha⟩ := hv.2 n; obtain ⟨b, hb⟩ := hw.2 n
    exact ⟨a + b, by rw [qCoeff_add, ha, hb, Int.cast_add]⟩⟩
  zero_mem' := ⟨W.zero_mem, fun n => ⟨0, by rw [qCoeff_zero, Int.cast_zero]⟩⟩
  smul_mem' z v hv := ⟨by rw [← Int.cast_smul_eq_zsmul ℂ]; exact W.smul_mem _ hv.1, fun n => by
    obtain ⟨a, ha⟩ := hv.2 n
    exact ⟨z * a, by rw [← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, ha, Int.cast_mul]⟩⟩

end Lattice
end RedRank
end P2MW.S_ModPForms_finiteDimensional_modPMod
