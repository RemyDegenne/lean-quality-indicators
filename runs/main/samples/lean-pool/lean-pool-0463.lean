section

section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularBackground

open Set Function Filter WeightedClasses LinearWaveBounds LocalizedWaveBounds

open CorrectionState CorrectionStep CorrectionInitialization

open scoped Topology ContDiff

section Isometry

variable {D E V I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem normal_reindex (e : D ≃ₗᵢ[ℝ] E) (a : WaveCoefficients E)
    (s : StripData E) (d : GraphDirections E) (n : ℕ) (x : D) :
    (ParticularWaveBounds.reindexCoefficients e a).normal
      (ParticularWaveBounds.reindexStrip e s) (ParticularWaveBounds.reindexDirections e d) n x =
      a.normal s d n (e x) := by
  simp only [WaveCoefficients.normal, HarmonicCalculus.phaseNormal, HarmonicCalculus.along,
    ParticularWaveBounds.reindexCoefficients, ParticularWaveBounds.reindexDirections,
    ParticularWaveBounds.reindexStrip, GraphDirections.radialField, GraphDirections.axialField,
    StateReindex.fderiv_pull, map_add, map_smul, e.apply_symm_apply]

end Isometry
end NavierStokes.ActualParticularBackground
end
end
end
end
