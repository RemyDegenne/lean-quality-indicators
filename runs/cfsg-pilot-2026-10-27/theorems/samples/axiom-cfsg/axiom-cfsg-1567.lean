public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup

open CFSG.Blueprint (LieModel)

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Counterexample4

theorem card_eq_81_of_L227 (c : Counterexample4 G)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) : Nat.card P = 81 := by
  have h := (k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).1
  rw [← card_map_subgroupOf_of_isPGroup c hZ hP.le hP.isPGroup]
  exact h

end Counterexample4
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
end
