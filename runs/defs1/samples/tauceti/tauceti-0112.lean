public section

namespace TauCeti

namespace TypeB2LieIndex

/-- Introduce a valid untwisted index `B₂(q)`. Validity forces `4 ≤ q.card`, by
`four_le_fieldOrder` below. -/
abbrev of (q : PrimePower) (hvalid : (LieTypeIndex.B 2 q).Valid) : TypeB2LieIndex :=
  ⟨RankTwoBLieIndex.ofB q hvalid, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩

end TypeB2LieIndex
end TauCeti
end
