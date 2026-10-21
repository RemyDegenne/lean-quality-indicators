namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal

open Filter MeasureTheory Set

namespace RadialTransition

theorem packing_ratio_le_density {s : ℝ} (hs : 0 ≤ s) :
    (packingNumber s : ℝ) / (s + 1) ^ 3 ≤ packingDensity :=
  le_csSup packing_ratios_bdd ⟨s, hs, rfl⟩

end RadialTransition
end
end OAI
