public section

open Set Function

open Filter Function Metric Set

open scoped Topology Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

macro_rules | `(tactic| gcongr_discharger) => `(tactic| apply ENNReal.summable)

namespace ENNReal

theorem tsum_toNNReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal :=
  congr($(tsum_congr fun x => (coe_toNNReal (hf x)).symm).toNNReal).trans
    NNReal.tsum_eq_toNNReal_tsum.symm

end ENNReal
end
