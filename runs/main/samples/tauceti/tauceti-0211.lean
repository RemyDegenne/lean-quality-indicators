public section

namespace TauCeti

open Subgroup

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

theorem isDemushkin_marked_of_q_two_odd_top (hG : IsDemushkin 2 G) (hodd : Odd (demushkinRank hG))
    (hrange : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    ∃ e : G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
        {demushkinWordTwoOddTop (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))},
      demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) _ 0)) = -1 ∧
        ∀ i : ℕ, i ≠ 0 → i < demushkinRank hG →
          demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) _ i)) = 1 := by
  obtain ⟨e⟩ :=
    hG.nonempty_continuousMulEquiv_presentedProP_demushkinWordTwoOddTop_of_range_eq hodd hrange
  obtain ⟨hfirst, htrivial⟩ :=
    demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoOddTop hG hodd e
  exact ⟨e, hfirst, fun i hi _ ↦ htrivial i hi⟩

end TauCeti
end
