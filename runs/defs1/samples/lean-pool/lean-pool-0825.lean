@[expose] public section

noncomputable section

namespace NavierStokes.SignedMeanGain

open Set Function Filter MeasureTheory

open scoped ContDiff Topology BigOperators

open WeightedClasses MeanIncrementBounds CorrectionState

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

namespace Geometry

/-- Domain, given by `PhysicalMeanDomain.slowDomain G.region.carrier`. -/
noncomputable def domain (G : Geometry) : Set Point := PhysicalMeanDomain.slowDomain
    G.region.carrier

end Geometry
end NavierStokes.SignedMeanGain
end
end
