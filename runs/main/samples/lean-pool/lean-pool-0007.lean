@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta

open DavisKahan

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

section SinTwoTheta

variable {𝕜 : Type*}

section SinTwoThetaIdentification

omit [CompleteSpace E] in
theorem starProjection_map_reflection (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection =
      conjByIsometryEquiv V.reflection U.starProjection := by
  ext x
  rw [Submodule.starProjection_map_apply]
  rfl

end SinTwoThetaIdentification
end SinTwoTheta
end DavisKahanExt
end TauCeti
end
