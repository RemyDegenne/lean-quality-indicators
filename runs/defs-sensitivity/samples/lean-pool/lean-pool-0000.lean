@[expose] public section

namespace LeanPool

open MeasureTheory Real

open _root_.ProbabilityTheory

open scoped BigOperators NNReal

noncomputable section

namespace HansonWright

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Frobenius norm of a finite real matrix. -/
def frobeniusNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sqrt (frobeniusNormSq A)

end HansonWright
end
end LeanPool
end
