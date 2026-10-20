@[expose] public section

namespace ExpGrowth

open ENNReal EReal Filter Function LinearGrowth

open scoped Topology

section composition

variable {u : ℕ → ℝ≥0∞} {v : ℕ → ℕ}

lemma _root_.Monotone.expGrowthInf_comp_le (h : Monotone u)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) :
    expGrowthInf (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp_le hv₀ hv₁

end composition
end ExpGrowth
end
