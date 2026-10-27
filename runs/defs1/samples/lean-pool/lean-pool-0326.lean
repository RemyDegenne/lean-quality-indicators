@[expose] public section

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The canonical intertwiner bundled as a unit in the acute regime. -/
noncomputable def spectraCanonicalIntertwinerUnit
    (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) : (H →L[𝕜] H)ˣ :=
  Units.oneSub (1 - spectraCanonicalIntertwiner U V)
    (norm_one_sub_spectraCanonicalIntertwiner_lt_one U V hacute)

end DavisKahan
end TauCeti
end
