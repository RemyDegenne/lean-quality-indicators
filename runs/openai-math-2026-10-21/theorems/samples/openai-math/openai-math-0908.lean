namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

open MeasureTheory Set

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

lemma radialPoint_mem_box {m k : ℕ} (hk : k ≤ m) (side : Fin 4) :
    radialPoint (2*m) side k ∈ box (2*m) := by
  fin_cases side <;> simp [radialPoint,mem_box] <;> omega

end TriangularLipschitz
end
end
end OAI
