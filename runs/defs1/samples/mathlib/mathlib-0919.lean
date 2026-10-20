@[expose] public section

noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 E F : Type*}

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]

variable [ContinuousConstSMul 𝕜 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

variable (𝕜 E) in
/-- There is a canonical map `E → WeakSpace 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

end Semiring
end
end
