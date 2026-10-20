@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

attribute [instance] LocallyFiniteTriangleComplex.vertexDecidableEq

attribute [instance] LocallyFiniteTriangleComplex.faceDecidableEq

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (K : LocallyFiniteTriangleComplex S)

theorem isClosed_iUnion_edgeCarrier_notMem [T2Space S] (v : K.Vertex) :
    IsClosed (⋃ e : {e : K.Edge // v ∉ e.1}, K.edgeCarrier e.1) := by
  apply (K.locallyFinite_edgeCarriers.comp_injective Subtype.val_injective).isClosed_iUnion
  intro e
  exact K.isClosed_edgeCarrier e.1

end LocallyFiniteTriangleComplex
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
