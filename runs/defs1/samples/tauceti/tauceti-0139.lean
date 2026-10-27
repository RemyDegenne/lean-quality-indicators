public section

namespace TauCeti

namespace GridDiagram

variable (n : ℕ)

/-- The standard `2 × 2` grid diagram with `O` markings on the identity state and `X`
markings on the transposition state. This is the usual smallest grid diagram for the unknot. -/
abbrev twoByTwo : GridDiagram 2 where
  O := GridState.twoByTwoId
  X := GridState.twoByTwoSwap
  disjoint := by
    intro c h
    fin_cases c <;> simp at h

end GridDiagram
end TauCeti
end
