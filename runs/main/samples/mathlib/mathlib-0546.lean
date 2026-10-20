@[expose] public section

open Set

open scoped NNReal ENNReal

noncomputable section

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

variable {s t : Set X} {ε δ : ℝ≥0∞} {x : X} {y : Y}

namespace AreSeparated

@[simp]
theorem empty_left (s : Set X) : AreSeparated ∅ s :=
  ⟨1, one_ne_zero, fun _x => False.elim⟩

end AreSeparated
end Metric
end
end
