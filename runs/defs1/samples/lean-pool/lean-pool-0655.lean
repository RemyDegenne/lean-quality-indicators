@[expose] public section

open scoped BigOperators

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

variable [AdaptiveSafety K U]

variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- The `adaptiveVertexPoint` declaration. -/
noncomputable def adaptiveVertexPoint (t : K.AdaptiveFace U)
    (v : K.AdaptiveVertexOccurrence U t) : K.realization :=
  K.levelFaceVertexPoint t.2.1 v

end IntrinsicTwoComplex
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
