@[expose] public section

noncomputable section

namespace NavierStokes.MovingMomentBounds

open Set Filter MeasureTheory CorrectionState WeightedClasses MeanIncrementBounds

open VariableGaugeMean LocalSignedRequest

open scoped ContDiff Topology BigOperators

open Set Filter MeasureTheory CorrectionState WeightedClasses MeanIncrementBounds

open VariableGaugeMean LocalSignedRequest

open scoped ContDiff Topology BigOperators

section Support

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

namespace Support

variable {a b : ℝ} {ell : S → ℝ} {U : Set S} {f g : ScalarField (PressureStream.Lift S)}

theorem directional (hf : Support a b ell U f) (hU : IsOpen U) (hl : ContinuousOn ell U)
    (v : PressureStream.Lift S) : Support a b ell U (fun n x => fderiv ℝ (f n) x v) :=
  fun n => fderiv_apply_supportedGauge hU hl (hf n) (fun _ => v)

end Support
end Support
end NavierStokes.MovingMomentBounds
end
end
