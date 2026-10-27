public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

open B6

theorem isUniqueMaxOver_iff {H T M : Subgroup G} :
    IsUniqueMaxOver H T M ↔
      IsMaxSubgroupIn H M ∧ T ≤ M ∧ ∀ N, IsMaxSubgroupIn H N → T ≤ N → N = M := by
  unfold IsUniqueMaxOver
  constructor
  · intro h
    have hM : M ∈ maxOver H T := by rw [h]; exact rfl
    exact ⟨hM.1, hM.2, fun N hN hTN => by
      have : N ∈ maxOver H T := ⟨hN, hTN⟩
      rw [h] at this
      exact this⟩
  · rintro ⟨hM, hTM, hu⟩
    ext N
    constructor
    · intro hN
      exact hu N hN.1 hN.2
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      exact ⟨hM, hTM⟩

end CFSG.Quasithin
end
