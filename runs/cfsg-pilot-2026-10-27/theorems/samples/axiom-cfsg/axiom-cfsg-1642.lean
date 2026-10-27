public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

open CFSG.ComponentClassification.RankTwoExceptional.Exc

open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam weylOne_conj_fam weylTwo_conj_fam
  weylCheck1 weylCheck2)

open CFSG.LieType.Ree.LargeReeCover (f4i)

section Blocks

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem rankOneGroupOne_le_gens
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    rankOneGroupOne K m ≤ closure (gens K [24, 33]) := by
  rw [← (CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model
    hm hK).1.1]
  refine reeLocalBlock_le_closure_gens _ fun α hα => ?_
  rcases fixedOrbitRootList_pos.1 α hα with h | h
  · exact ⟨24, by simp, (eq_of_vecEq h).symm⟩
  · exact ⟨33, by simp, (eq_of_vecEq h).symm⟩

end Blocks
end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
end
