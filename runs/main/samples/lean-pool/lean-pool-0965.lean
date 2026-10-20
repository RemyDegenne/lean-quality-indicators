@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace SharedFoundations

namespace Spectral

open scoped InnerProductSpace

open DavisKahanExt

open TauCeti.DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace BoundedSpectralSelection

theorem projection_eq_starProjection
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    S.projection = S.subspace.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  rw [S.projection_eq]
  calc
    boundedSelfAdjointSpectralProjection A S.selfAdjoint S.carrier
          S.measurable_carrier x =
        (boundedSelfAdjointSpectralSubspace A S.selfAdjoint S.carrier
          S.measurable_carrier).starProjection x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (boundedSelfAdjointSpectralProjection_eq_starProjection
          A S.selfAdjoint S.carrier S.measurable_carrier)
    _ = S.subspace.starProjection x :=
      starProjection_apply_congr S.subspace_eq.symm x

end BoundedSpectralSelection
end Spectral
end SharedFoundations
end DavisKahan
end TauCeti
end
