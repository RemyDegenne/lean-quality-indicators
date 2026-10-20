public section

namespace TauCeti

namespace TypeB2LieIndex

/-- The untwisted rank-two family `B₂(q)`, regarded as an ordinary-or-graph-twisted index through
its specialization to the general type-`B` family. -/
abbrev toGraphTwistedIndex (d : TypeB2LieIndex) : GraphTwistedIndex :=
  d.toTypeBLieIndex.toGraphTwistedIndex

end TypeB2LieIndex
end TauCeti
end
