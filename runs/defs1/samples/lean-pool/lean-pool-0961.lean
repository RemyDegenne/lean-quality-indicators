@[expose] public section

open scoped BigOperators

namespace O3

/-- The squared Euclidean norm of the gradient at an execution query. -/
noncomputable def ogmgGradientSq (cfg : OGMGExecutionConfig d) (i : ℕ) : ℝ :=
  (lpNorm 2 (ogmgGradient cfg i)) ^ (2 : ℕ)

end O3
end
