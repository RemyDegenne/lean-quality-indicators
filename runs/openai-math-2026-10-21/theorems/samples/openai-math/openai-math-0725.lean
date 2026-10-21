namespace OAI

noncomputable section

open scoped Topology NNReal

open Filter

namespace TraceCone

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable [PartialOrder A]

namespace CuntzBelow

theorem eq_zero [StarOrderedRing A] {a : Positive A}
    (h : CuntzBelow a Positive.zero) : a.1 = 0 := by
  by_contra ha
  obtain ⟨v, hv⟩ := h ‖a.1‖ (norm_pos_iff.mpr ha)
  simp [Positive.zero] at hv

end CuntzBelow
end TraceCone
end
end OAI
