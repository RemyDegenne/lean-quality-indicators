@[expose] public section

variable {𝕜 𝕜' E F ι : Type*}

open Set Filter Function

open scoped Topology Pointwise

namespace Bornology

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [TopologicalSpace E]

variable [ContinuousSMul 𝕜 E]

theorem isVonNBounded_singleton (x : E) : IsVonNBounded 𝕜 ({x} : Set E) := fun _ hV =>
  (absorbent_nhds_zero hV).absorbs

end NormedField
end Bornology
end
