public section

noncomputable section

open TensorProduct

open scoped TensorProduct

namespace AlgebraicGeometry

universe u v w w₁ w₂

variable (K : Type u) [CommRing K] (V : Type v) [AddCommGroup V] [Module K V]
  (R : Type w) [CommRing R] [Algebra K R]

/-- A separate type carries the scalar structure transported to the literal
source-order tensor product. It creates no module instance on `V ⊗[K] R`. -/
structure SourceOrderedTensor where
  /-- The literal tensor with the coefficient algebra on the right. -/
  tensor : V ⊗[K] R

end AlgebraicGeometry
end
end
