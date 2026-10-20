@[expose] public section

universe u

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem exists_continuous_coset_representative (H : Subgroup G)
    [IsClosed (H : Set G)] :
    ∃ s : C(G ⧸ H, G), ∀ q, QuotientGroup.mk (s q) = q := by
  let _ : IsClosed ((⊥ : Subgroup G) : Set G) := ⟨by simp⟩
  obtain ⟨s, hs, hright⟩ :=
    quotientMapOfLE_exists_continuous_section_of_isClosed
      (K := (⊥ : Subgroup G)) (H := H) bot_le
  refine ⟨⟨quotientBotHomeomorph ∘ s,
    quotientBotHomeomorph.continuous.comp hs⟩, ?_⟩
  intro q
  have hprojection (x : G ⧸ (⊥ : Subgroup G)) :
      QuotientGroup.mk (quotientBotHomeomorph x) =
        quotientMapOfLE (bot_le : (⊥ : Subgroup G) ≤ H) x := by
    induction x using Quotient.inductionOn with
    | _ g =>
      simp only [quotientBotHomeomorph_apply_mk, quotientMapOfLE_apply_mk]
  exact (hprojection (s q)).trans (hright q)

end Subgroup
end
