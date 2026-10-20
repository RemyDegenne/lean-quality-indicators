@[expose] public section

noncomputable section

local notation "𝕊" => Circle

open MeasureTheory Filter

open scoped Topology

open scoped Real

namespace Real

open FourierTransform

variable {V W E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
  [FiniteDimensional ℝ W]

open scoped RealInnerProductSpace

variable [FiniteDimensional ℝ V]

open scoped BoundedContinuousFunction

/-- The inverse Fourier transform from `L1` functions to bounded continuous functions. -/
def Lp.fourierTransformInv (f : Lp (α := V) E 1) : V →ᵇ E :=
  (Lp.fourierTransform f).compContinuous (-ContinuousMap.id V)

end Real
end
end
