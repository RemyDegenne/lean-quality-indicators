@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace NormalForm

open SurfaceCellComplex

/-- The one-face incidence presentation carried by the canonical nonorientable word. -/
abbrev nonOrientableCellComplex (p n : ℕ) : SurfaceCellComplex :=
  oneFacePresentation (NonOrientableEdge p n) (nonOrientableBoundaryWord p n)

end NormalForm
end ClassificationOfSurfaces
end Topology
end LeanEval
end
