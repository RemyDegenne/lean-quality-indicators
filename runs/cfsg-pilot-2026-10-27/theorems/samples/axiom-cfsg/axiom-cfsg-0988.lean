public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem B_elemAb (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {Γ : Subgroup G} {η : G} (hη : η ∈ Γ) (hΓ : Γ ≤ ModSplit.normDY d.D₂ d.Y)
    (hηfix : ∀ y ∈ d.Y, η * y * η⁻¹ = y → y = 1) :
    (∀ x ∈ ModSplit.liftFixG d.D₂ d.Y Γ, ∀ y ∈ ModSplit.liftFixG d.D₂ d.Y Γ, x * y = y * x) ∧
      ∀ x ∈ ModSplit.liftFixG d.D₂ d.Y Γ, x * x = 1 := by
  have hmem : ∀ {x : G}, x ∈ ModSplit.liftFixG d.D₂ d.Y Γ →
      x ∈ d.D₂ ∧ η * x * η⁻¹ * x⁻¹ ∈ d.Y := fun {x} hx => by
    obtain ⟨h1, h2⟩ := (ModSplit.mem_liftFixG_iff _ _ hΓ).1 hx
    exact ⟨h1, h2 η hη⟩
  constructor
  · intro x₁ hx₁ x₂ hx₂
    obtain ⟨hD₁, hz₁⟩ := hmem hx₁
    obtain ⟨hD₂', hz₂⟩ := hmem hx₂
    obtain ⟨z₁, hz₁def⟩ : ∃ z₁ : G, z₁ = η * x₁ * η⁻¹ * x₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨z₂, hz₂def⟩ : ∃ z₂ : G, z₂ = η * x₂ * η⁻¹ * x₂⁻¹ := ⟨_, rfl⟩
    rw [← hz₁def] at hz₁
    rw [← hz₂def] at hz₂
    have e1 : η * x₁ * η⁻¹ = z₁ * x₁ := by rw [hz₁def]; group
    have e2 : η * x₂ * η⁻¹ = z₂ * x₂ := by rw [hz₂def]; group
    have hc : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ d.Y := h.D₂_commutator_mem_Y hK hD₁ hD₂'
    have hfixc : η * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * η⁻¹ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by
      have e : η * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * η⁻¹ =
          (η * x₁ * η⁻¹) * (η * x₂ * η⁻¹) * (η * x₁ * η⁻¹)⁻¹ * (η * x₂ * η⁻¹)⁻¹ := by group
      rw [e, e1, e2, comm_mul_left_Y hz₁ hD₁ (d.D₂.mul_mem (h.Y_le_D₂ hz₂) hD₂'),
        comm_mul_right_Y hz₂ hD₁ hD₂']
    have h1 := hηfix _ hc hfixc
    calc x₁ * x₂ = (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * (x₂ * x₁) := by group
      _ = x₂ * x₁ := by rw [h1, one_mul]
  · intro x hx
    obtain ⟨hD, hz⟩ := hmem hx
    obtain ⟨z, hzdef⟩ : ∃ z : G, z = η * x * η⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hzdef] at hz
    have e1 : η * x * η⁻¹ = z * x := by rw [hzdef]; group
    have hxz : x * z = z * x := Data.Hyp.D₂_comm_Y' hD hz
    have hs : x * x ∈ d.Y := h.D₂_mul_self_mem_Y hK hD
    have hfix2 : η * (x * x) * η⁻¹ = x * x := by
      have e : η * (x * x) * η⁻¹ = (η * x * η⁻¹) * (η * x * η⁻¹) := by group
      rw [e, e1]
      calc (z * x) * (z * x) = z * (x * z) * x := by group
        _ = z * (z * x) * x := by rw [hxz]
        _ = (z * z) * (x * x) := by group
        _ = x * x := by rw [h.Y_sq hz, one_mul]
    exact hηfix _ hs hfix2

end Data.Hyp
end C7
end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
end
