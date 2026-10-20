@[expose] public section

namespace EuclideanGeometry

namespace Sphere

open AffineSubspace

open scoped RealInnerProductSpace Affine

variable {V P : Type*}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The affine subspace `as` is tangent to the sphere `s` at the point `p`. -/
structure IsTangentAt (s : Sphere P) (p : P) (as : AffineSubspace ℝ P) : Prop where
  mem_sphere : p ∈ s
  mem_space : p ∈ as
  le_orthRadius : as ≤ s.orthRadius p

end Sphere
end EuclideanGeometry
end
