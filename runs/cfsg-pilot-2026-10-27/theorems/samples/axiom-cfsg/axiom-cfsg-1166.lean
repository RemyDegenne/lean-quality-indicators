public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG.Assembly.RankThreeEven (projSL projSU)

section Easy

theorem noCQOf_j1 :
    NoCQOf (Spor .J1) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J1 ≃* Spor .J1 := b
  refine NoCQOf.of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J1.card_J1]
  norm_num

end Easy
end CFSG.RankThree.PartTwo.Sec4.Ronan148S
end
