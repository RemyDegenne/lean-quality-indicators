public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Late

open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalClosureIn_le {M : Subgroup G} {c : G} (hc : c ∈ M) : normalClosureIn M c ≤ M := by
  rw [normalClosureIn, Subgroup.closure_le]
  rintro _ ⟨m, hm, rfl⟩
  exact M.mul_mem (M.mul_mem hm hc) (M.inv_mem hm)

end CFSG.RankThree.PartTwo.Sec20
end
