@[expose] public section

noncomputable section

namespace NavierStokes.PrimaryCopyBounds

open Set Function Filter PhaseJetBounds PrimaryPulseBounds WeightedClasses

open scoped Topology ContDiff BigOperators InnerProductSpace

variable {ι : Type*} {D : Type} {E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

section ConstructedPulse

variable {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}

/-- Pulse envelope, defined pointwise by `referenceP ((F j).lam i) ((F j).u i) ((F j).L i) ((F
j).L i * (χ i x).2)`. -/
noncomputable def pulseEnvelope (F : Fin 2 → PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ι → D → ℝ := fun i x =>
  referenceP ((F j).lam i) ((F j).u i) ((F j).L i) ((F j).L i * (χ i x).2)

end ConstructedPulse
end NavierStokes.PrimaryCopyBounds
end
end
