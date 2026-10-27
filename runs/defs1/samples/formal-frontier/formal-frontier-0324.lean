@[expose] public section

open Bundle Bornology

open scoped ComplexConjugate

namespace Bundle

section RealFiberwise

variable {B : Type*} {E : B → Type*}
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]

/-- Regard Mathlib's real Riemannian metric data as Hermitian metric data over `ℝ`. -/
def HermitianMetric.ofRiemannianMetric (g : RiemannianMetric E) : HermitianMetric ℝ E where
  inner := g.inner
  symm b v w := g.symm b w v
  pos := g.pos
  continuousAt := g.continuousAt
  isVonNBounded := g.isVonNBounded

end RealFiberwise
end Bundle
end
