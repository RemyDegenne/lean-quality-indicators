@[expose] public section

attribute [instance 100] AddTorsor.nonempty

attribute [instance 100] Torsor.nonempty

section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

@[to_additive ]
theorem smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂) := by
  apply smul_right_cancel p₂
  rw [sdiv_smul, mul_smul, sdiv_smul]

end General
end
