namespace OAI

noncomputable section

open Set Filter Topology Metric Polynomial

open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex

namespace DegeneratingTrees.Clock

lemma rootCoord_inverse_power {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    (rootCoord n x)^(-(n:ℤ)) = x := by
  rw [rootCoord_zpow hx]
  have hd : -(-((n:ℤ):ℝ))/(n:ℝ) = 1 := by
    push_cast
    field_simp
  push_cast at *
  rw [hd,Real.rpow_one]

end DegeneratingTrees.Clock
end
end OAI
