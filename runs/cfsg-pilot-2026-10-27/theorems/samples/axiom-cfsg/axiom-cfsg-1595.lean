public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem card_dvd_two_mul_inf_K (h : T6Ctx N u p) {E : Subgroup G}
    (hE : ∀ e ∈ E, e ∈ N.K₁ ⊔ N.K₂ ⊔ N.S) :
    Nat.card ↥E ∣ 2 * Nat.card ↥(E ⊓ (N.K₁ ⊔ N.K₂)) := by
  have hSn : N.S ≤ Subgroup.normalizer ((N.K₁ ⊔ N.K₂ : Subgroup G) : Set G) := fun s hs =>
    Subgroup.mem_normalizer_fintype (S_norm_K h hs)
  obtain ⟨a, haS, ha⟩ := (Subgroup.relIndex_eq_two_iff.1 h.sec5.loc.S_idx)
  have key : ∀ e ∈ E, e ∉ N.K₁ ⊔ N.K₂ → ∀ e' ∈ E, e' ∉ N.K₁ ⊔ N.K₂ → e' * e⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
    intro e he heK e' he' he'K
    obtain ⟨k, hk, s, hs, rfl⟩ := t6_mem_sup_of_le_normalizer hSn (hE e he)
    obtain ⟨k', hk', s', hs', rfl⟩ := t6_mem_sup_of_le_normalizer hSn (hE e' he')
    have hsK : s ∉ N.S ⊓ (N.K₁ ⊔ N.K₂) := fun hh =>
      heK (Subgroup.mul_mem _ hk hh.2)
    have hs'K : s' ∉ N.S ⊓ (N.K₁ ⊔ N.K₂) := fun hh =>
      he'K (Subgroup.mul_mem _ hk' hh.2)
    have h1 : s * a ∈ N.S ⊓ (N.K₁ ⊔ N.K₂) := by
      rcases ha s hs with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact hx
      · exact absurd hx hsK
    have h1' : s' * a ∈ N.S ⊓ (N.K₁ ⊔ N.K₂) := by
      rcases ha s' hs' with ⟨hx, -⟩ | ⟨hx, -⟩
      · exact hx
      · exact absurd hx hs'K
    have hss : s' * s⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
      have := (N.S ⊓ (N.K₁ ⊔ N.K₂)).mul_mem h1' ((N.S ⊓ (N.K₁ ⊔ N.K₂)).inv_mem h1)
      have e : s' * a * (s * a)⁻¹ = s' * s⁻¹ := by group
      rw [e] at this
      exact this.2
    have e : k' * s' * (k * s)⁻¹ = k' * (s' * s⁻¹) * k⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk' hss) (Subgroup.inv_mem _ hk)
  have hrel : (N.K₁ ⊔ N.K₂).relIndex E ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hall : ∀ e ∈ E, e ∈ N.K₁ ⊔ N.K₂
    · exact ⟨1, E.one_mem, fun b hb => Or.inr (hall b hb)⟩
    · push Not at hall
      obtain ⟨e₀, he₀, he₀K⟩ := hall
      refine ⟨e₀⁻¹, E.inv_mem he₀, fun b hb => ?_⟩
      by_cases hbK : b ∈ N.K₁ ⊔ N.K₂
      · exact Or.inr hbK
      · exact Or.inl (key e₀ he₀ he₀K b hb hbK)
  have hmul := Subgroup.relIndex_mul_card (N.K₁ ⊔ N.K₂) E
  rw [inf_comm] at hmul
  rw [← hmul]
  exact Nat.mul_dvd_mul_right hrel _

end CFSG.GH74.GLS.Stage4.Rest.T6
end
