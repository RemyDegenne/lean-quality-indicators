public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_top_of_sup_center_eq_top' {Q : Type*} [Group Q] (hQ : commutator Q = ⊤)
    {H : Subgroup Q} (h : H ⊔ center Q = ⊤) : H = ⊤ := by
  rw [eq_top_iff, ← hQ, commutator_eq_closure, closure_le]
  rintro _ ⟨a, b, rfl⟩
  have ha : a ∈ H ⊔ center Q := by rw [h]; trivial
  have hb : b ∈ H ⊔ center Q := by rw [h]; trivial
  obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
  obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
  have hc₁ := mem_center_iff.mp hz₁
  have hc₂ := mem_center_iff.mp hz₂
  have e : ⁅h₁ * z₁, h₂ * z₂⁆ = ⁅h₁, h₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc h₁ * z₁ * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹
        = h₁ * (z₁ * h₂) * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by group
      _ = h₁ * (h₂ * z₁) * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by rw [hc₁ h₂]
      _ = h₁ * h₂ * (z₁ * z₂ * z₁⁻¹) * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by group
      _ = h₁ * h₂ * z₂ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by
          rw [show z₁ * z₂ * z₁⁻¹ = z₂ by rw [hc₂ z₁]; group]
      _ = h₁ * h₂ * (z₂ * h₁⁻¹) * z₂⁻¹ * h₂⁻¹ := by group
      _ = h₁ * h₂ * (h₁⁻¹ * z₂) * z₂⁻¹ * h₂⁻¹ := by rw [hc₂ h₁⁻¹]
      _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by group
  rw [SetLike.mem_coe, e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hh₁ hh₂) (inv_mem hh₁)) (inv_mem hh₂)

end CFSG.ComponentClassification.Sol76
end
