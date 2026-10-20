@[expose] public section

noncomputable section

namespace NavierStokes.StateReindex

open Set Filter Function HarmonicCalculus

open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem block_waveBounds (e : D ≃ₗᵢ[ℝ] E) {s : WeightedClasses.StripData E}
    {w : ℕ → E → ℝ} {alpha : ℝ} {b : CorrectionState.HarmonicBlock E}
    (hb : b.WaveBounds s w alpha) :
    (block e b).WaveBounds (strip e s) (fun n x => w n (e x)) alpha := by
  intro i j hj
  exact ParticularWaveBounds.waveClass_reindex e (hb i j hj)

end NavierStokes.StateReindex
end
end
