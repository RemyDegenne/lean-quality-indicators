@[expose] public section

namespace TauCeti

namespace DavisKahan.Angle

open DavisKahan

open TauCeti.RealComplexification

open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped InnerProductSpace

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

noncomputable section

universe u w v

variable {𝕜 : Type u} [RCLike 𝕜]

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

section Directed

/-- **The paper's directed `sin Θ₀`** between an ordered pair of closed subspaces, at an
arbitrary `RCLike` field: the modulus of the cross-projection `U → Uᗮ` through `V`. -/
def directedSinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  ContinuousLinearMap.modulus (Vᗮ.starProjection ∘L U.starProjection)

end Directed
end
end DavisKahan.Angle
end TauCeti
end
