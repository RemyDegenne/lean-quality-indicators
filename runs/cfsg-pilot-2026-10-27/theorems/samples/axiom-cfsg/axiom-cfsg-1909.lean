public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

open scoped commutatorElement

variable {G : Type*} [Group G]

namespace BlockFactorContainment

variable [Finite G] {J : Subgroup G}

theorem mem_blockInvolutions_of_mem (hJ : IsUniversalComponent J) (heven : Even (Nat.card J))
    (hΔ : (block J).Nontrivial) {A : Subgroup G} (hA : A ∈ block J) {a : G} (haA : a ∈ A)
    (ha2 : orderOf a = 2) : a ∈ blockInvolutions J := by
  obtain ⟨L, hL, hLA⟩ := hΔ.exists_ne A
  rcases commRel_of_mem_block hJ heven hA hL with h | h
  · exact absurd h.symm hLA
  · exact ⟨ha2, L, hL, Subgroup.commutator_eq_bot_iff_le_centralizer.1 h haA⟩

end BlockFactorContainment
end CFSG.LocalAnalysis.ComponentInitial
end
