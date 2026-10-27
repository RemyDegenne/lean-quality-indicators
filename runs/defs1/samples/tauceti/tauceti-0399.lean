public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

variable {x z : GridState n}
  (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
  (hcommon : D.first.left = D.second.left)
  (hcol : D.second.right ∈ Grid.cIoo D.first.left D.first.right)
  (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)

variable (x z) in
/-- The initial-side pentagon--rectangle partners obtained by recutting the counted
common-initial-side cross sources: the exact recut image of
`GridDiagram.initialPentagonInitialCrossOverlapSources`. -/
noncomputable def initialPentagonInitialCrossOverlapPartners :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonInitialCrossOverlapSources C x z).attach.map
    ⟨G.initialPentagonInitialCrossOverlapPartner C,
      G.initialPentagonInitialCrossOverlapPartner_injective C⟩

end GridDiagram
end TauCeti
end
