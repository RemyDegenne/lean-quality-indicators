public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction.Hyp

open scoped commutatorElement

variable {G : Type} [Group G] (M : Subgroup G) [M.Normal]

theorem map_le_centralizer {P U : Subgroup G} (h : P ≤ centralizer (U : Set G)) :
    P.map (cq M) ≤ centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M)) := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (h hx) u hu]

end CFSG.EvenSporadicStandard.Induction.Junction
end
