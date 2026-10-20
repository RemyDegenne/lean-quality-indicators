@[expose] public section

noncomputable section

namespace NavierStokes.SignedMeanGain

open Set Function Filter MeasureTheory

open scoped ContDiff Topology BigOperators

open WeightedClasses MeanIncrementBounds CorrectionState

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- These hypotheses concern local regularity and the actual incoming
state. None is a bound or a cancellation assertion about the updated residual. -/
structure LocalData (G : Geometry) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point) : Prop
        where
  operators_eq : c.operators = G.operators
  base : SmoothTriple G.strip.domain c.base
  mean : SmoothTriple G.strip.domain u.mean
  covariance : ∀ i j, SmoothOn G.strip.domain (u.covariance i j)
  theta : SmoothOn G.domain (u.thetaResidual c)
  axial : SmoothOn G.domain (u.axialResidual c)
  theta_support : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord
    G.region.carrier (u.thetaResidual c n)
  axial_support : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord
    G.region.carrier (u.axialResidual c n)
  angular_flux : GaugeMomentBalances.MovingAngularInputs G.region G.patch.a G.patch.b c u
  axial_flux : GaugeMomentBalances.MovingAxialInputs G.region G.patch.a G.patch.b c u
  source : MovingField G (u.gr c)
  updated_source : MovingField G ((waveStage G.gauge c u w q gaussian).gr c)
  reconstructed : VariableGaugeMean.reconstructState G.gauge c u = u
  angular_mass : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0
  axial_mass : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0

end NavierStokes.SignedMeanGain
end
end
