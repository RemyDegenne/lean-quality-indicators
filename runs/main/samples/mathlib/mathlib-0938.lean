public section

open scoped CompactlySupported

open Metric ENNReal NNReal Filter Set Topology TopologicalSpace MeasureTheory
  BoundedContinuousFunction

section Forward

open FiniteMeasure

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]

variable (E) in
lemma isCompact_setOfPred_finiteMeasure_eq_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C} := by
  have : {μ : FiniteMeasure E | μ.mass = C} = {μ | μ.mass ≤ C} ∩ {μ | μ.mass = C} := by grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOfPred_finiteMeasure_le_of_compactSpace E C)
  exact isClosed_eq (by fun_prop) (by fun_prop)

end Forward
end
