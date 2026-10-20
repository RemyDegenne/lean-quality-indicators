@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace SurfaceCellComplex

namespace OccurrencePairingValid

theorem interior_occurs_twice {K : SurfaceCellComplex} (h : K.OccurrencePairingValid)
    (d : K.Dart) (hd : ¬K.IsBoundaryDart d) : K.OccursExactlyTwice d := by
  exact h.surface_valid.occurs_twice_of_not_boundary hd

end OccurrencePairingValid
end SurfaceCellComplex
end ClassificationOfSurfaces
end Topology
end LeanEval
end
