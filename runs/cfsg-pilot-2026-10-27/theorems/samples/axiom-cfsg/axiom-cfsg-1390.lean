public section

namespace CFSG.Quasithin

open Subgroup

section

variable {G : Type*} [Group G]

theorem card_le_two_mul_card_centralizer [Finite G] {z : G} (hz : z * z = 1) {A : Subgroup G}
    (q : G) (hcomm : ∀ a ∈ A, a * q * a⁻¹ * q⁻¹ = 1 ∨ a * q * a⁻¹ * q⁻¹ = z)
    (hcentral : ∀ a ∈ A, a * z = z * a) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) := by
  classical
  by_cases hA : A ≤ Subgroup.centralizer ({q} : Set G)
  · rw [inf_eq_left.2 hA]; omega
  · obtain ⟨a₀, ha₀, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hA
    have hmem : ∀ a ∈ A, a ∈ Subgroup.centralizer ({q} : Set G) ↔ a * q = q * a := by
      intro a _
      exact Subgroup.mem_centralizer_singleton_iff
    have hz0 : ∀ a ∈ A, a * q ≠ q * a → a * q = z * (q * a) := by
      intro a ha hne
      rcases hcomm a ha with h | h
      · exact absurd (by
          calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
            _ = q * a := by rw [h, one_mul]) hne
      · calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
          _ = z * (q * a) := by rw [h]
    have hsub : (A : Set G) ⊆ ↑(A ⊓ Subgroup.centralizer ({q} : Set G)) ∪
        (fun c => a₀ * c) '' ↑(A ⊓ Subgroup.centralizer ({q} : Set G)) := by
      intro a ha
      by_cases haC : a ∈ Subgroup.centralizer ({q} : Set G)
      · exact Or.inl ⟨ha, haC⟩
      · refine Or.inr ⟨a₀⁻¹ * a, ⟨A.mul_mem (A.inv_mem ha₀) ha, ?_⟩, by group⟩
        show a₀⁻¹ * a ∈ Subgroup.centralizer ({q} : Set G)
        rw [hmem _ (A.mul_mem (A.inv_mem ha₀) ha)]
        have hne : a * q ≠ q * a := fun h => haC ((hmem a ha).2 h)
        have hne₀ : a₀ * q ≠ q * a₀ := fun h => ha₀C ((hmem a₀ ha₀).2 h)
        have h1 := hz0 a ha hne
        have h2 := hz0 a₀ ha₀ hne₀
        have hza : a₀⁻¹ * z = z * a₀⁻¹ := hcentral _ (A.inv_mem ha₀)
        have hq0 : a₀⁻¹ * q = z * (q * a₀⁻¹) := by
          calc a₀⁻¹ * q = a₀⁻¹ * (q * a₀) * a₀⁻¹ := by group
            _ = a₀⁻¹ * (z * (a₀ * q)) * a₀⁻¹ := by
              rw [show q * a₀ = z * (a₀ * q) from by
                calc q * a₀ = z * (z * (q * a₀)) := by rw [← mul_assoc, hz, one_mul]
                  _ = z * (a₀ * q) := by rw [h2]]
            _ = z * (q * a₀⁻¹) := by
              calc a₀⁻¹ * (z * (a₀ * q)) * a₀⁻¹ = (a₀⁻¹ * z) * (a₀ * q) * a₀⁻¹ := by group
                _ = (z * a₀⁻¹) * (a₀ * q) * a₀⁻¹ := by rw [hza]
                _ = z * q * a₀⁻¹ := by group
                _ = z * (q * a₀⁻¹) := by group
        calc a₀⁻¹ * a * q = a₀⁻¹ * (a * q) := by group
          _ = a₀⁻¹ * (z * (q * a)) := by rw [h1]
          _ = (a₀⁻¹ * z) * (q * a) := by group
          _ = (z * a₀⁻¹) * (q * a) := by rw [hza]
          _ = z * ((a₀⁻¹ * q) * a) := by group
          _ = z * ((z * (q * a₀⁻¹)) * a) := by rw [hq0]
          _ = (z * z) * (q * (a₀⁻¹ * a)) := by group
          _ = q * (a₀⁻¹ * a) := by rw [hz, one_mul]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (↑(A ⊓ Subgroup.centralizer ({q} : Set G)) : Set G)
      ((fun c => a₀ * c) '' ↑(A ⊓ Subgroup.centralizer ({q} : Set G)))
    rw [Set.ncard_image_of_injective _ (mul_right_injective a₀)] at h2
    have e1 : Nat.card ↥A = (A : Set G).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) =
        (↑(A ⊓ Subgroup.centralizer ({q} : Set G)) : Set G).ncard := Nat.card_coe_set_eq _
    omega

end
end CFSG.Quasithin
end
