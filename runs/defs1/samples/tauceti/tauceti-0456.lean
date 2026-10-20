public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  {x z : GridState n}

/-- The counted common-terminal-side rectangle--pentagon domains whose recuts stay in the
rectangle--pentagon sum. The initial side of the rectangle is strictly inside the
pentagon's column interval. -/
noncomputable def terminalSelfPairSources (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectanglePentagonDecompositions C x z).filter fun D =>
    D.rectangle.right = D.pentagon.right ∧
      D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right

end TauCeti.GridDiagram
end
