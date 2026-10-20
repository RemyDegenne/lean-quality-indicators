@[expose] public section

open Cardinal Module Module Set Submodule

universe u v

section Module

variable {K : Type u} {V : Type v} [Ring K] [StrongRankCondition K] [AddCommGroup V] [Module K V]

theorem rank_submodule_le_one_iff' (s : Submodule K V) [Module.Free K s] :
    Module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ := by
  constructor
  · rw [rank_submodule_le_one_iff]
    rintro ⟨v₀, _, h⟩
    exact ⟨v₀, h⟩
  · rintro ⟨v₀, h⟩
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := s)
    simpa [b.mk_eq_rank''] using b.linearIndependent.map' _ (ker_inclusion _ _ h)
      |>.cardinal_le_rank.trans (rank_span_le {v₀})

end Module
end
