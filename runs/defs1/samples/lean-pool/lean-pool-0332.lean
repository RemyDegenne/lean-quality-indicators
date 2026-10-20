@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Cancellation

/-- A one-face word with a negatively displayed inverse pair. -/
@[reducible]
def negativeNamedSource {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ([.neg a, .pos a] ++ X)

end Cancellation
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
