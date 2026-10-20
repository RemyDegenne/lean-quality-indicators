public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

@[simp]
theorem mem_initialPentagonInitialSelfSources
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.initialPentagonInitialSelfSources C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧
        D.first.left = D.second.left ∧
          D.first.right ∈ Grid.cIoo D.second.left D.second.right := by
  classical
  simp [initialPentagonInitialSelfSources]

end GridDiagram
end TauCeti
end
