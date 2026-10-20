public section

namespace TauCeti

open Subgroup

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace IsDemushkin

section Dyadic

variable (hG : IsDemushkin 2 G)

include hG

theorem range_demushkinCharacter_ne_unitsPlusMinus_of_demushkinRank_eq_two
    (hn : demushkinRank hG = 2) {f : ℕ} (hf : 2 ≤ f) :
    (demushkinCharacter hG).toMonoidHom.range ≠ unitsPlusMinus f := fun h ↦ by
  obtain ⟨u, hu⟩ :=
    hG.exists_topologicalClosure_zpowers_eq_range_demushkinCharacter_of_demushkinRank_eq_two hn
  exact not_exists_topologicalClosure_zpowers_eq_unitsPlusMinus hf ⟨u, hu.trans h⟩

end Dyadic
end IsDemushkin
end TauCeti
end
