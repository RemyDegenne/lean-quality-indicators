public section

namespace CFSG.RankThree.PartOne.CTP.Alt

open Equiv Equiv.Perm

theorem closure_centralizers_eq_top {G V : Type*} [Group G] [Fintype V] [DecidableEq V]
    (hV₁ : 11 ≤ Fintype.card V) (hV₂ : Fintype.card V ≤ 14)
    (φ : G →* Perm V) (hφ : Function.Injective φ) (hrange : φ.range = alternatingGroup V)
    {E : Subgroup G} (hE : Nat.card E = 25) (hpow : ∀ x ∈ E, x ^ 5 = 1) :
    Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hcard : Nat.card (E.map φ) = 25 := by
    rw [Subgroup.card_map_of_injective hφ]
    exact hE
  have hpow' : ∀ y ∈ E.map φ, y ^ 5 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hmain := alternatingGroup_le_closure_centralizers hV₁ hV₂ hcard hpow'
  have h2 : Subgroup.closure {k : Perm V | k ∈ alternatingGroup V ∧
      ∃ x ∈ E.map φ, x ≠ 1 ∧ k * x = x * k} ≤
      (Subgroup.closure {k : G | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}).map φ := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro k ⟨hk, x', ⟨x, hx, rfl⟩, hx1, hkx⟩
    rw [← hrange] at hk
    obtain ⟨g, rfl⟩ := hk
    refine ⟨g, ⟨x, hx, ?_, ?_⟩, rfl⟩
    · intro h
      exact hx1 (by rw [h, map_one])
    · apply hφ
      simpa using hkx
  rw [eq_top_iff]
  intro g _
  have hg : φ g ∈ alternatingGroup V := by
    rw [← hrange]
    exact ⟨g, rfl⟩
  obtain ⟨t, ht, hφt⟩ := h2 (hmain hg)
  rwa [← hφ hφt]

end CFSG.RankThree.PartOne.CTP.Alt
end
