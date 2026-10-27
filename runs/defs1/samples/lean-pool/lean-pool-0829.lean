@[expose] public section

noncomputable section

namespace NavierStokes.StateReindex

open Set Filter Function HarmonicCalculus

open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Operators, bundling `epsilon`, `radialFrequency`, `fastCoefficient`, `radius` and the
required compatibility proofs. -/
noncomputable def operators (e : D ≃ₗᵢ[ℝ] E) (o : MeanIncrementBounds.Operators E) :
    MeanIncrementBounds.Operators D where
  epsilon := o.epsilon
  radialFrequency := o.radialFrequency
  fastCoefficient := o.fastCoefficient
  radius := fun x => o.radius (e x)
  radialProfile := fun x => o.radialProfile (e x)
  eR := e.symm o.eR
  eZ := e.symm o.eZ
  eT := e.symm o.eT
  vR := e.symm o.vR
  vT := e.symm o.vT

end NavierStokes.StateReindex
end
end
