public section

open MeasureTheory Set Filter

open scoped ENNReal Topology

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

theorem lpsCat_of_ge {α : Type} {b : ℝ} {f g : ParabolicPoint → α} {z : ParabolicPoint}
    (h : b ≤ z.2) : lpsCat b f g z = g z := by
  simp [lpsCat, not_lt.mpr h]

end ESS
end
end
