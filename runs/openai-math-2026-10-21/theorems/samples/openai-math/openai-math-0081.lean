namespace OAI

noncomputable section

namespace KadisonSimilarity

open MeasureTheory

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [instance] PublishedSeparableModel.measurable PublishedSeparableModel.normed
  PublishedSeparableModel.inner PublishedSeparableModel.complete
  PublishedSeparableModel.separableFiber

theorem universalHyperreflexivity_of_published (inputs : PublishedUniformInputs.{u}) :
    UniversalHyperreflexivity.{u} universalConstant := by
  intro K _ _ _ M T
  exact hyperreflexivity_of_spectralSteps_and_arveson M (spectralStepApproximation M.commutant) T
    (le_of_lt universalConstant_pos) (arvesonDistanceFormula M T)
    (uniformCommutatorEstimate_of_published inputs K M.commutant)

end KadisonSimilarity
end
end OAI
