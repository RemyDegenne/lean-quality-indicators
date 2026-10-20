@[expose] public section

open Bundle Bornology

open scoped ComplexConjugate

namespace Bundle

section RealFiberwise

variable {B : Type*} {E : B → Type*}
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]

/-- Exact identification of Hermitian metric data over `ℝ` with Mathlib's Riemannian metric data. -/
@[simps apply symm_apply]
def HermitianMetric.realEquiv : HermitianMetric ℝ E ≃ RiemannianMetric E where
  toFun := HermitianMetric.toRiemannianMetric
  invFun := HermitianMetric.ofRiemannianMetric
  left_inv := HermitianMetric.ofRiemannianMetric_toRiemannianMetric
  right_inv := HermitianMetric.toRiemannianMetric_ofRiemannianMetric

end RealFiberwise
end Bundle
end
