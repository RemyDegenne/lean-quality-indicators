public section

namespace CFSG.GroupTheory

theorem card_le_of_mulEquiv_of_sylow {G G' : Type*} [Group G] [Finite G] [Group G']
    (ε : G ≃* G') {n : ℕ}
    (h' : ∀ (P : Sylow 3 G') (A : Subgroup G'), (∀ e ∈ A, e * e = 1) →
      (∀ e ∈ A, ∀ f ∈ A, e * f = f * e) → (∀ t ∈ P, ∀ x ∈ A, t * x * t⁻¹ ∈ A) →
      Nat.card ↥A ≤ n)
    (P : Sylow 3 G) (A : Subgroup G) (hA2 : ∀ e ∈ A, e * e = 1)
    (hAc : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e) (hAP : ∀ t ∈ P, ∀ x ∈ A, t * x * t⁻¹ ∈ A) :
    Nat.card ↥A ≤ n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective ε.toMonoidHom := ε.surjective
  set P' : Sylow 3 G' := Sylow.mapSurjective (f := ε.toMonoidHom) hsurj P with hP'
  have hmem : ∀ t' ∈ P', ∃ t ∈ P, ε t = t' := by
    intro t' ht'
    have ht'' : t' ∈ (P : Subgroup G).map ε.toMonoidHom := ht'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ht''
    exact ⟨t, ht, rfl⟩
  have key := h' P' (A.map ε.toMonoidHom) (by
      rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, hA2 e he, map_one]) (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hAc e he f hf]) (by
      intro t' ht' x' hx'
      obtain ⟨t, ht, rfl⟩ := hmem t' ht'
      obtain ⟨x, hx, rfl⟩ := hx'
      refine ⟨t * x * t⁻¹, hAP t ht x hx, ?_⟩
      simp [map_mul, map_inv])
  rwa [Subgroup.card_map_of_injective ε.injective] at key

end CFSG.GroupTheory
end
