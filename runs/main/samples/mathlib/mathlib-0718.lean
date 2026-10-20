@[expose] public section

attribute [instance 100] AddTorsor.nonempty

attribute [instance 100] Torsor.nonempty

section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

@[to_additive (attr := simp) ]
theorem inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁ := by
  refine inv_eq_of_mul_eq_one_right (smul_right_cancel p₁ ?_)
  rw [sdiv_mul_sdiv_cancel, sdiv_self]

end General
end
