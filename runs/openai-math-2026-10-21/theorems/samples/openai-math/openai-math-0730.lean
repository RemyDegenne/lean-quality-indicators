namespace OAI

namespace BackwardIntertwiners

open Filter

open scoped Topology

noncomputable section

open Topology MeasureTheory Set

open scoped ENNReal

open scoped Classical

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpace : CompleteSpace H]

lemma strongGenerated_commutative {s : Set (H →L[ℂ] H)}
    (hs : ∀ A ∈ s, IsSelfAdjoint A) (hc : ∀ A ∈ s, ∀ B ∈ s, A*B=B*A) :
    ∀ A ∈ strongGenerated s, ∀ B ∈ strongGenerated s, A*B=B*A := by
  have hle : strongGenerated s ≤ StarSubalgebra.centralizer ℂ s := by
    apply strongGenerated_le (strong_centralizer_closed s)
    intro B hB
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    exact ⟨hc A hA B hB, by rw [(hs A hA).star_eq]; exact hc A hA B hB⟩
  have hle' : strongGenerated s ≤ StarSubalgebra.centralizer ℂ (strongGenerated s : Set _) := by
    apply strongGenerated_le (strong_centralizer_closed _)
    intro B hB
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    refine ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA) B hB).1.symm, ?_⟩
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle ((strongGenerated s).star_mem' hA)) B hB).1.symm
  intro A hA B hB
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle' hB) A hA).1

end
end BackwardIntertwiners
end OAI
