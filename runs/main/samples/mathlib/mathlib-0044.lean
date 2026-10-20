@[expose] public section

open Function ENNReal NNReal Set

noncomputable section

namespace EReal

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℝ} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

end EReal
end
end
