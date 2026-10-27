@[expose] public section

namespace FD1D

noncomputable section

open MeasureTheory

open ProbabilityTheory

open scoped BigOperators ENNReal

namespace FiniteKernel

variable {α : Type*} [Fintype α]

/-- A project `FiniteKernel`, viewed as a Mathlib Markov kernel. -/
noncomputable def toKernel [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : FiniteKernel α) : Kernel α α where
  toFun x := (K.rowLaw x).toMeasure
  measurable' := measurable_of_finite _

end FiniteKernel
end
end FD1D
end
