section

@[expose] public section

noncomputable section

namespace NavierStokes.ErrorHarmonics

open Set Filter Function MeasureTheory

open HarmonicFields CorrectionState

open scoped BigOperators ContDiff Topology ComplexConjugate

section GaussianErrors

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The retained Gaussian term as a literal real carrier field. -/
noncomputable def gaussianField (d : LinearWaveBounds.GraphDirections (D × ℝ))
    (ψ : ℕ → D × ℝ → ℝ) (a source : ℕ → D × ℝ → HarmonicCalculus.ComplexVector)
    (j : ℤ) (k : ℕ → ℝ) (Ψ : ℕ → D × ℝ → ℝ) : Oscillation D :=
  fun n p i => (HarmonicCalculus.vectorMode (k n * (j : ℝ)) (Ψ n)
    (LinearWaveBounds.excludedSlotError d ψ a source n) p i).re

end GaussianErrors
end NavierStokes.ErrorHarmonics
end
end
end
