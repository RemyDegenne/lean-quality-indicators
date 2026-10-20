@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace SurfaceCellComplex

/-- Relabel arbitrary darts as signed `Fin`-labelled unoriented edges. -/
noncomputable def finSignedDartEquiv
    (K : SurfaceCellComplex) (hinv : ∀ d, K.inv d ≠ d) :
    K.Dart ≃ SignedDart (Fin K.numEdgeOrbits) :=
  (K.signedDartEquiv hinv).symm.trans
    (SignedDart.mapEquiv (Fintype.equivFin K.EdgeOrbit))

end SurfaceCellComplex
end ClassificationOfSurfaces
end Topology
end LeanEval
end
