@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

/-- The selected source cell, cyclically aligned and then cut by the local degenerate disk
homeomorphism. -/
noncomputable def rightDegenerateSelectedCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    PolygonCell (P.boundary cut.face.face).length ≃ₜ
      DiskSquare.ParamChildGluing
        cut.left.length cut.right.length :=
  (PolygonCell.rotateHomeomorph
    (sourceBoundaryLength_eq_rightLength P cut hleft)
    (positiveCutRotation P cut horientation)).trans
    ((P2DegenerateDisk.sourceChildGluingHomeomorph
      cut.right.length hr).trans
      (zeroLeftChildGluingHomeomorph
        (leftLength_eq_zero hleft)))

end P2
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
