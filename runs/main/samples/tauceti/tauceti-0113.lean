public section

namespace TauCeti

namespace DualGraph

open Finset

variable (r : ℕ) [NeZero r]

variable {r}

@[simp]
theorem valence_cycle (v : ZMod r) : (cycle r).valence v = 2 := by
  rw [valence_def, card_eq_two]
  refine ⟨(v, 0), (v - 1, 1), by simp, ?_⟩
  ext ⟨e, i⟩
  fin_cases i <;> simp [eq_sub_iff_add_eq]

end DualGraph
end TauCeti
end
