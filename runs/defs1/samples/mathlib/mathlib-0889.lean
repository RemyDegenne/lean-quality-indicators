@[expose] public section

open Topology

section UniqueUnital

section NNReal

open NNReal

variable {X : Type*} [TopologicalSpace X]

namespace ContinuousMap

/-- This map sends `f : C(X, ℝ)` to `Real.toNNReal ∘ f`, bundled as a continuous map `C(X, ℝ≥0)`. -/
noncomputable def toNNReal (f : C(X, ℝ)) : C(X, ℝ≥0) := .realToNNReal |>.comp f

end ContinuousMap
end NNReal
end UniqueUnital
end
