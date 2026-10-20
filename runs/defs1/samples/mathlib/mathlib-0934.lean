@[expose] public section

open Set

open scoped ENNReal NNReal

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  {A B C : Set X} {ε δ : ℝ≥0} {x : X}

section Definitions

/-- The external covering number of a set `A` in `X` for radius `ε` is the minimal cardinality
(in `ℕ∞`) of an `ε`-cover by points in `X` (not necessarily in `A`). -/
noncomputable
def externalCoveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞ :=
  ⨅ (C : Set X) (_ : IsCover ε A C), C.encard

end Definitions
end Metric
end
