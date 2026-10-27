public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G]

variable [Finite G] {S T M W₁ W₂ : Subgroup G}

theorem IsTypePPair.exists_isTypePPair_of_isWitnessedPConfiguration {N A B E : Subgroup G}
    (hp : IsTypePPair M N A B) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    ∃ T : Subgroup G, IsTypePPair M T W₁ W₂ := by
  have hsolv : Group.IsSolvable ↥M := hp.isSolvable M hp.ne_top_left
  obtain ⟨U₀, -, hU₀⟩ := hp.exists_compatible_left
  obtain ⟨y, hyM, hA, hB⟩ :=
    eq_of_isWitnessedPConfiguration_of_map_conj hU₀.1 hc hc.sup_commutator_W₁
      hc.disjoint_commutator_W₁
  have h2 := hp.map_conj y⁻¹
  rw [map_conj_eq_self (inv_mem hyM), hA, hB] at h2
  exact ⟨_, h2⟩

end CFSG.FeitThompson
end
