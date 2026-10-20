public section

namespace TauCeti

open Relation

variable {k : ℕ}

variable {D₁ D₂ D₃ : BrauerDiagram k}

theorem middleLoopCount_add_middleLoopCount_composeDiagram (D₁ D₂ D₃ : BrauerDiagram k) :
    middleLoopCount D₁ D₂ + middleLoopCount (composeDiagram D₁ D₂) D₃ =
      middleLoopCount D₂ D₃ + middleLoopCount D₁ (composeDiagram D₂ D₃) := by
  rw [← tripleLoopCount_eq, ← tripleLoopCount_flip, tripleLoopCount_eq, middleLoopCount_flip,
    ← flip_composeDiagram, middleLoopCount_flip]

end TauCeti
end
