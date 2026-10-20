@[expose] public section

open Bundle Bornology

open scoped ComplexConjugate

namespace Bundle

section RealContinuous

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

@[simp]
theorem ContinuousHermitianMetric.toRiemannianMetric_inner (g : ContinuousHermitianMetric ℝ F E)
    (b : B) (v w : E b) : g.toRiemannianMetric.inner b v w = g.inner b v w := rfl

end RealContinuous
end Bundle
end
