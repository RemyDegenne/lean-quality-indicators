@[expose] public section

open Bundle Bornology

open scoped ComplexConjugate

namespace Bundle

section Continuous

variable (𝕜 : Type*) [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

variable {𝕜 F E}

/-- Forget continuity in the base while preserving the fiber metric and its topology. -/
def ContinuousHermitianMetric.toHermitianMetric (g : ContinuousHermitianMetric 𝕜 F E) :
    HermitianMetric 𝕜 E where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  continuousAt := g.continuousAt
  isVonNBounded := g.isVonNBounded

end Continuous
end Bundle
end
