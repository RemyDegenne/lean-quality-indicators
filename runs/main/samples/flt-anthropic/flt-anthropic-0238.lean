namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_basis_forall_apply_eq_sum_single_sub_single_smul_of_typeOne

set_option autoImplicit false

namespace KSpec

noncomputable section

section Piece

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem eq_zero_of_mem_inf_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hNM : N ≤ M₀) {w : W} (hwN : w ∈ N) (hwP : w ∈ orthoIn M₀ N B hlin hNM) : w = 0 := by
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hwP
  by_contra hne
  have h := hpos w hwM hne
  rw [hperp w hwN, Complex.zero_re] at h
  exact lt_irrefl _ h

end Piece
end
end KSpec
end P2MW.S_LanglandsTunnell_CubicInduction_exists_basis_forall_apply_eq_sum_single_sub_single_smul_of_typeOne
