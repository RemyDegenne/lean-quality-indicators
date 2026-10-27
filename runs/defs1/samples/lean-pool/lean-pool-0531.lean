@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

open scoped InnerProductSpace

open scoped Topology

open scoped ENNReal

open Filter

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

attribute [instance] KyFanDominantIdealFamily.isComplete

namespace KyFanDominantIdealFamily

variable (N : KyFanDominantIdealFamily.{u, v} 𝕜)

/-- The ordinary operator norm with its finite-Ky-Fan dominance property. -/
noncomputable def operatorNorm :
    KyFanDominantIdealFamily.{u, v} 𝕜 where
  toSymmetricOperatorIdealFamily := TauCeti.operatorNormFamily 𝕜
  isComplete := inferInstance
  gauge_le_of_forall_kyFanApproximationGauge_le := by
    intro E F E' F' _ _ _ _ _ _ _ _ _ _ _ _ A B hmajor
    have h : ‖A‖ ≤ ‖B‖ := by simpa using hmajor 1
    simpa [TauCeti.gauge_operatorNormFamily, ← ofReal_norm] using
      ENNReal.ofReal_le_ofReal h

end KyFanDominantIdealFamily
end ExactSinTheta
end DavisKahan
end TauCeti
end
