public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Assembly.LowTwoRank

open CFSG.AGLEmbedding (centerQuotientAction centerQuotientAction_eq mk_eq_mk_iff_conjNormal_eq)

section Commutator

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem exists_commutator_eq_of_mem_inf_sup (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hcomm : ∀ c₁ ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X),
      ∀ c₂ ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), c₁ * c₂ = c₂ * c₁)
    {u v : X} (hu : u ∈ (R : Subgroup X)) (hv : v ∈ (R : Subgroup X))
    (huK : u ∈ K ⊔ Subgroup.centralizer (K : Set X))
    (hvK : v ∈ K ⊔ Subgroup.centralizer (K : Set X)) :
    ∃ t₁ ∈ (R : Subgroup X) ⊓ K, ∃ t₂ ∈ (R : Subgroup X) ⊓ K,
      u * v * u⁻¹ * v⁻¹ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by
  obtain ⟨t₁, ht₁, c₁, hc₁, rfl⟩ := exists_mul_eq_of_mem_inf_sup R hu huK
  obtain ⟨t₂, ht₂, c₂, hc₂, rfl⟩ := exists_mul_eq_of_mem_inf_sup R hv hvK
  refine ⟨t₁, ht₁, t₂, ht₂, ?_⟩
  have e1 : c₁ * t₂ = t₂ * c₁ := (Subgroup.mem_centralizer_iff.mp hc₁.2 t₂ ht₂.2).symm
  have e2 : c₂ * t₁⁻¹ = t₁⁻¹ * c₂ :=
    (Subgroup.mem_centralizer_iff.mp hc₂.2 t₁⁻¹ (K.inv_mem ht₁.2)).symm
  have e3 : c₁ * c₂ = c₂ * c₁ := hcomm c₁ hc₁ c₂ hc₂
  calc t₁ * c₁ * (t₂ * c₂) * (t₁ * c₁)⁻¹ * (t₂ * c₂)⁻¹
      = t₁ * (c₁ * t₂) * c₂ * c₁⁻¹ * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by group
    _ = t₁ * t₂ * (c₁ * c₂) * c₁⁻¹ * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by rw [e1]; group
    _ = t₁ * t₂ * c₂ * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by rw [e3]; group
    _ = t₁ * t₂ * (c₂ * t₁⁻¹) * c₂⁻¹ * t₂⁻¹ := by group
    _ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by rw [e2]; group

end Commutator
end CFSG.LocalAnalysis.RankThreeTheoremC
end
