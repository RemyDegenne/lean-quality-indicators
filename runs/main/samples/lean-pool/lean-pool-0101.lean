@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

section Fibre

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
theorem measurable_prodMk_coordinateProcess (theta : Theta) (s : NNReal) :
    Measurable (fun omega : ContinuousPath alpha ↦ (theta, omega s)) :=
  measurable_const.prodMk (ContinuousPath.measurable_coordinateProcess (alpha := alpha) s)

end Fibre
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess
end
