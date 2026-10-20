@[expose] public section

open Function ENNReal NNReal Set

noncomputable section

namespace EReal

@[simp]
lemma toENNReal_pos_iff {x : EReal} : 0 < x.toENNReal ↔ 0 < x := by
  rw [pos_iff_ne_zero, toENNReal_ne_zero_iff]

end EReal
end
end
