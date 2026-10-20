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

theorem pulseVector_jets (F : Fin 2 → PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i)
    (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1)
    (j : Fin 2) : NativeJets V (pulseEnvelope F χ j) (pulseVector F χ j) :=
  NativeJets.of_envelope ((F j).pulse_jets.comp hχ hscale hmap)

end ConstructedPulse
end NavierStokes.PrimaryCopyBounds
end
end
