@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

section

section ContinuousProcess

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

section QuenchedExpectations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_integral_finsetEvaluation_continuousProcess (I : Finset NNReal)
    (f : (I → alpha) → E) (hf : StronglyMeasurable f) :
    Measurable fun p : Theta × alpha ↦
      ∫ eta, f (ContinuousPath.finsetEvaluation I eta)
        ∂IsConservative.continuousProcess P hP p := by
  have hI : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) (t : NNReal)
  exact measurable_integral_continuousProcess P hP _ (hf.comp_measurable hI)

end QuenchedExpectations
end ContinuousProcess
end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess
end PortComputability
end
