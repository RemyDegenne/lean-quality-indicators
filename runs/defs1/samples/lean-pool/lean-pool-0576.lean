@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

/-- A rotated source side lying in the right cut piece, viewed with its local right index. -/
noncomputable def positiveRightSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    Fin cut.right.length :=
  ⟨(positiveCutSideIndex P cut horientation hl hr i).val -
      cut.left.length,
    by
      have hbound :=
        (positiveCutSideIndex P cut horientation hl hr i).isLt
      omega⟩

end P2
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
