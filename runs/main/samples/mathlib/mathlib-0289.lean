@[expose] public section

open NNReal ENNReal BoundedContinuousFunction Set Metric Filter

open scoped Topology

noncomputable section thickenedIndicator

variable {α : Type*} [PseudoEMetricSpace α]

theorem indicator_le_thickenedIndicatorAux (δ : ℝ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ thickenedIndicatorAux δ E := by
  intro a
  by_cases h : a ∈ E
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

end thickenedIndicator
end
