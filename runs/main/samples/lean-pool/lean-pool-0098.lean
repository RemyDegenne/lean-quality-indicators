@[expose] public section

namespace TauCeti

namespace ApproximationNumber

open scoped InnerProductSpace

open scoped Topology

open Filter

universe u v vF vG vH vE0 vF0 w

variable {𝕜 : Type u} [RCLike 𝕜]

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem kyFanApproximationGauge_nonneg
    (k : ℕ) (K : E →L[𝕜] F) :
    0 ≤ kyFanApproximationGauge k K :=
  K.kyFanGauge_nonneg k

end ApproximationNumber
end TauCeti
end
