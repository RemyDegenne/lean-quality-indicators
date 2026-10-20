@[expose] public section

open TauCeti.DavisKahan.Angle

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

namespace FreeBeam

namespace Model

open DavisKahan1970.Section9

noncomputable section

/-- **The Rayleigh--Ritz residual column map.**  It sends a trial vector `v` to the
part of `(A + ε t) v` orthogonal to the trial subspace. -/
def beamRitzColumnMap (ε : ℝ) : beamTrial →L[ℂ] BeamL2 :=
  (ContinuousLinearMap.id ℂ BeamL2 - beamTrial.starProjection) ∘L beamResidual ε

end
end Model
end FreeBeam
end DavisKahan
end TauCeti
end
