@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

theorem zeroLeftChildPair_generator_map
    {l r : ℕ} (hl : l = 0)
    {x y : DiskSquare.ChildPair 0 r}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 r x y) :
    DiskSquare.ParamChildSeamGenerator l r
      (zeroLeftChildPairHomeomorph hl x)
      (zeroLeftChildPairHomeomorph hl y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator l r
          (.inl
            (zeroLeftCellHomeomorph hl
              (PolygonCell.side (0 : Fin 1) t)))
          (.inr
            (PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t)))
      rw [zeroLeftCellHomeomorph_side]
      exact DiskSquare.ParamChildSeamGenerator.glue t

end P2
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
