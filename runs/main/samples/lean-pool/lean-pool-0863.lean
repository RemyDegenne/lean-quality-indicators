@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

namespace FiniteCyclicPresentation.SignedPresentationIso

open SurfaceCellComplex

variable {P Q : FiniteCyclicPresentation}

theorem preHomeomorph_pairing_parameter_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (e.mapPairing validQ pairing).identification.target.point
        ((e.mapPairing validQ pairing).identification.parameter t) := by
  rw [e.preHomeomorph_pairing_target_point]
  rfl

end FiniteCyclicPresentation.SignedPresentationIso
end LeanEval.Topology.ClassificationOfSurfaces
end
