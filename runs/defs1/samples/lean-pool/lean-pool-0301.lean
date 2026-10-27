@[expose] public section

noncomputable section

open scoped ContDiff

namespace EulerPhysicalL2Scaling

open Finset MeasureTheory EulerSmoothLimit

/-- Derivative sum, given by `∑ n ∈ range (m+1), lpNorm (iteratedFDeriv ℝ n f) 2 volume`. -/
def derivativeSum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (f : Space → V) : ℝ :=
  ∑ n ∈ range (m+1), lpNorm (iteratedFDeriv ℝ n f) 2 volume

end EulerPhysicalL2Scaling
end
end
