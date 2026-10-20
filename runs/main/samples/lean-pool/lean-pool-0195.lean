section

@[expose] public section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal

namespace NavierStokesR3.LocalizedTensorBounds

open ProblemStatement Comparison

theorem continuous_component {f : Space → Space} (hf : Continuous f) (i : Fin 3) :
    Continuous (fun x => f x i) :=
  (continuous_apply i).comp ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp hf)

end NavierStokesR3.LocalizedTensorBounds
end
end
end
