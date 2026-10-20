public section

open Function

open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rightInverse_timeDependentFlow (v : ℝ → E → E) {K : ℝ≥0}
    (hv : LipschitzWith K (timeDependentSuspension v)) (s t : ℝ) :
    RightInverse (timeDependentFlow v hv t s) (timeDependentFlow v hv s t) :=
  fun _ ↦ by simp

end TauCeti
end
