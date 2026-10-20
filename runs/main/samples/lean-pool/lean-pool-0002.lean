@[expose] public section

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
theorem canonicalIntertwiner_apply_sourceDefect_eq_zero
    (x : halmosSourceDefect U V) :
    spectraCanonicalIntertwiner U V (x : H) = 0 := by
  obtain ⟨hPx, hQperpx⟩ := mem_halmosSourceDefect.mp x.property
  have hP : U.starProjection (x : H) = x :=
    Submodule.starProjection_eq_self_iff.mpr hPx
  have hQ : V.starProjection (x : H) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hQperpx
  have hPc : (Uᗮ).starProjection (x : H) = 0 := by
    simp [hP]
  simp [spectraCanonicalIntertwiner, hP, hQ, hPc]

end
end DavisKahan
end TauCeti
end
