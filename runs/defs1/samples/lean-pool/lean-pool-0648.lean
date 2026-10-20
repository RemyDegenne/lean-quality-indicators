@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

noncomputable section

universe u v w x y

variable {𝕜 : Type u} [RCLike 𝕜]

section Basic

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The `k`th **Ky Fan gauge**: the sum of the first `k` approximation numbers. -/
def kyFanGauge (T : E →L[𝕜] F) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range k, T.approximationNumber n

end Basic
end
end ContinuousLinearMap
end
