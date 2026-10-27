@[expose] public section

noncomputable section

namespace EulerMeanCoefficients

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal Filter

open scoped ContDiff BoundedContinuousFunction Topology

section BoundedFields

variable {V : Type*} [NormedAddCommGroup V]

/-- Translated, given by `A.compContinuous ⟨fun x => x+a, continuous_id.add continuous_const⟩`. -/
def translated (A : Space →ᵇ V) (a : Space) : Space →ᵇ V :=
  A.compContinuous ⟨fun x => x+a, continuous_id.add continuous_const⟩

end BoundedFields
end EulerMeanCoefficients
end
end
