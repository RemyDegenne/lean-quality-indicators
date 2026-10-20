@[expose] public section

open Set

open scoped NNReal

namespace Metric

variable {X Y : Type*}

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {ε δ : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

@[simp] lemma IsCover.refl (ε : ℝ≥0) (s : Set X) : IsCover ε s s := .rfl

end PseudoEMetricSpace
end Metric
end
