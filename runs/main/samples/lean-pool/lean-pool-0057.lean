@[expose] public section

open Finset

namespace Utilities

variable {H : CFGraph}

lemma mem_botSet {g : firingScript H} {v : H.V} :
    v ∈ botSet g ↔ ∀ u, g v ≤ g u := by
  rw [botSet, mem_topSet]
  constructor
  · intro h u
    have := h u
    simp only [Pi.neg_apply] at this
    omega
  · intro h u
    have := h u
    simp only [Pi.neg_apply]
    omega

end Utilities
end
