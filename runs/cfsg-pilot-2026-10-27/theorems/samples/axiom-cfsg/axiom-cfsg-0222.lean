public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native TauCeti

open CFSG.Assembly.RankThreeEven (localRank)

section Odd

theorem three_le_localRank_of_mem_odd (s : SporadicName) (hs : s ∈ [.Ly, .Suz, .ONan, .HN])
    [Finite (CFSGIndex.sporadic s).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic s).Group := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact three_le_localRank_Ly
  · exact three_le_localRank_Suz
  · exact three_le_localRank_ONan
  · exact three_le_localRank_HN

end Odd
end CFSG.RankThree.PartTwo.Census
end
