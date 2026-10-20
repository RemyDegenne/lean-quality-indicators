public section

open Pointwise Topology

namespace TauCeti.Huber

section Values

variable {k : ℕ} {A B : Type*} [CommSemiring A] [CommSemiring B] [TopologicalSpace B]

@[simp]
theorem weightedEval_zero (φ : A →+* B) (b : Fin k → B) :
    weightedEval φ b (0 : MvPowerSeries (Fin k) A) = 0 := by
  simp [weightedEval_def, weightedEvalTerm_def]

end Values
end TauCeti.Huber
end
