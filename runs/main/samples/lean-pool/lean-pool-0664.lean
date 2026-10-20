@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan1970

open DavisKahan

open DavisKahan.Proposition35

noncomputable section

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

theorem corollary3_2_directRotation_swap
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) =
      star (nonacuteDirectRotation U V J) :=
  nonacuteDirectRotation_swap U V J

end Generic
end
end DavisKahan1970
end TauCeti
end
