public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

open CFSG.SeitzReduction.LinearPilot (diagUnit coe_diagUnit)

open scoped MatrixGroups

variable {K : Type} [Field K]

theorem commute_range_shortBlock_longRootSp2 {s v : StatedSp 3 K}
    (hs : s ∈ (shortBlock K one_ne_two_three).range) (hv : v ∈ longRootSp2 K 3 (0 : Fin 3)) :
    Commute s v := by
  obtain ⟨A, rfl⟩ := hs
  have hY : shortBlock K one_ne_two_three A ∈ complSp K (0 : Fin 3) := by
    rw [mem_complSp]
    intro x y hxy
    refine isSupp_shortBlock one_ne_two_three A x y fun h => hxy ⟨?_, ?_⟩
    · rcases h.1 with hx | hx <;> rcases mem_coords.1 hx with rfl | rfl <;> simp [mem_coords]
    · rcases h.2 with hy | hy <;> rcases mem_coords.1 hy with rfl | rfl <;> simp [mem_coords]
  exact (commute_of_mem_longRootSp2_of_mem_complSp hv hY).symm

end CFSG.SeitzReduction.SymplecticPilot
end
