@[expose] public section

namespace HadwigerNelsonBounds

/-- A compressed coloring-tree node: a forced stem followed by a branch/leaf. -/
structure PartsTreeNode where
  /-- Unary forced assignments preceding the branch. -/
  stem : List PartsAssignment
  /-- Vertex branched on after the forced stem. -/
  vertex : Fin 481
  /-- Encoded child index for each color, with zero meaning absent. -/
  children : Fin 4 → Nat

end HadwigerNelsonBounds
end
