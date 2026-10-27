@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal BigOperators

namespace QuadraticCarleson

namespace KrauseLaceyNonstandardOneNodeClosure

open KrauseLaceyBadScale KrauseLaceyScalarNear

noncomputable
section

/-- The dimensionless scale weight in the nonstandard interpolation. -/
def oneNodeNonstandardScaleWeight (s : ℕ) : ℝ :=
  nonstandardScaleWeight s

end
end KrauseLaceyNonstandardOneNodeClosure
end QuadraticCarleson
end
