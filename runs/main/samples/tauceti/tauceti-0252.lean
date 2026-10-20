public section

open Finset

namespace TauCeti

variable {n : ℕ} {μ : YoungDiagram}

namespace GTPattern

theorem tableauEntry_mono (P : GTPattern n) (i : ℕ) {c c' : ℕ} (h : c ≤ c') :
    P.tableauEntry i c ≤ P.tableauEntry i c' := by
  refine card_le_card fun j hj => ?_
  simp only [mem_filter, mem_range] at hj ⊢
  exact ⟨hj.1, hj.2.trans (by exact_mod_cast h)⟩

end GTPattern
end TauCeti
end
