public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

open scoped MatrixGroups

theorem exists_mul_of_mem_sup {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hBN : B ≤ normalizer (A : Set G) := le_normalizer_of_conj_mem (fun b hb a ha => by
    rw [← h a ha b hb, mul_inv_cancel_right]
    exact ha) le_rfl
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left A B hBN] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

end CFSG.ComponentClassification.HarrisLit.T1.S74
end
