@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

open scoped BigOperators

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace EdgeRelabeling

/-- Compose signed-edge relabelings. Reversing twice cancels, so the reversal bits compose by
exclusive-or. -/
def trans {α β γ : Type*}
    (e : EdgeRelabeling α β) (f : EdgeRelabeling β γ) : EdgeRelabeling α γ where
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  reverse := fun a ↦ Bool.xor (e.reverse a) (f.reverse (e.edgeEquiv a))

end EdgeRelabeling
end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
end
