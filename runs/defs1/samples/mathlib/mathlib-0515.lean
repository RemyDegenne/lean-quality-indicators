@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

open PointsWithCircumcenterIndex

/-- The weights for a single vertex of a simplex, in terms of
`pointsWithCircumcenter`. -/
def pointWeightsWithCircumcenter {n : ℕ} (i : Fin (n + 1)) : PointsWithCircumcenterIndex n → ℝ
  | pointIndex j => if j = i then 1 else 0
  | circumcenterIndex => 0

end Simplex
end Affine
end
end
