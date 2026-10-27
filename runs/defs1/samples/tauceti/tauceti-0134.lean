public section

namespace TauCeti

/-- A validated index in the untwisted rank-two family `B₂(q)`. The Suzuki family, which shares the
diagram, is excluded by the outer predicate. -/
abbrev TypeB2LieIndex : Type _ := {d : RankTwoBLieIndex // ¬d.1.1.UsesHalfFrobenius}

end TauCeti
end
