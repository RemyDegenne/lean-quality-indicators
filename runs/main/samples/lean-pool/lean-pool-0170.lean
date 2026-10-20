@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

theorem positiveRealizationInvMap_childGluing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (q : DiskSquare.ParamChildGluing
      cut.left.length cut.right.length) :
    positiveRealizationInvMap P cut horientation hl hr validP
        (positiveChildGluingMap
          P cut horientation validP q) =
      positiveChildGluingInvMap
        P cut horientation hl hr validP q := by
  induction q using Quotient.inductionOn'
  case _ x =>
    cases x with
    | inl z =>
        rw [positiveChildGluingMap_mk]
        change
          positiveInvPreMap P cut horientation hl hr validP
              ⟨oldFace P cut cut.face.face,
                positiveSelectedChildCellHomeomorph
                  P cut horientation z⟩ =
            positiveChildGluingInvMap
              P cut horientation hl hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inl z))
        exact positiveInvPreMap_selectedChild_apply
          P cut horientation hl hr validP z
    | inr z =>
        rw [positiveChildGluingMap_mk]
        change
          positiveInvPreMap P cut horientation hl hr validP
              ⟨rightFace P cut,
                positiveRightChildCellHomeomorph
                  P cut horientation z⟩ =
            positiveChildGluingInvMap
              P cut horientation hl hr validP
              (@Quotient.mk''
                (DiskSquare.ChildPair
                  cut.left.length cut.right.length)
                (DiskSquare.paramChildSeamSetoid
                  cut.left.length cut.right.length)
                (.inr z))
        exact positiveInvPreMap_rightChild_apply
          P cut horientation hl hr validP z

end P2
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
