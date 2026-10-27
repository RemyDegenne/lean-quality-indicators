@[expose] public section

open MeasurableSpace

open scoped symmDiff

namespace MeasureTheory.VectorMeasure

variable {α : Type*} {hα : MeasurableSpace α} {E : Type*} [NormedAddCommGroup E]
  [CompleteSpace E] {μ : Measure α}

/-- A finitely additive vector measure which is dominated by a finite positive measure is in
fact countably additive. -/
def of_additive_of_le_measure
    (m : Set α → E) (hm : ∀ s, ‖m s‖ₑ ≤ μ s) [IsFiniteMeasure μ]
    (h'm : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t)
    (h''m : ∀ s, ¬ MeasurableSet s → m s = 0) : VectorMeasure α E where
  measureOf' := m
  empty' := by simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
  not_measurable' := h''m
  m_iUnion' f f_meas f_disj := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm]; swap
    · simp only [← toReal_enorm]
      apply ENNReal.summable_toReal
      apply ne_of_lt
      calc ∑' i, ‖m (f i)‖ₑ
      _ ≤ ∑' i, μ (f i) := by gcongr; apply hm
      _ = μ (⋃ i, f i) := (measure_iUnion f_disj f_meas).symm
      _ < ⊤ := measure_lt_top μ (⋃ i, f i)
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp_rw [norm_sub_rev, ← toReal_enorm, ← ENNReal.toReal_zero]
    apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    have A n : m (⋃ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range n, m (f i) := by
      induction n with
      | zero => simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
      | succ n ih =>
        simp only [Finset.range_add_one]
        rw [Finset.sum_insert (by simp)]
        simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
        rw [h'm _ _ (f_meas n), ih]
        · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
        · simp only [Finset.mem_range, Set.disjoint_iUnion_right]
          intro i hi
          exact f_disj hi.ne'
    have B n : m (⋃ i, f i) = m (⋃ i ∈ Finset.range n, f i) + m (⋃ i ∈ Set.Ici n, f i) := by
      have : ⋃ i, f i = (⋃ i ∈ Finset.range n, f i) ∪ (⋃ i ∈ Set.Ici n, f i) := by
        ext; simp; grind
      rw [this]
      apply h'm
      · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
      · exact MeasurableSet.biUnion (Set.to_countable _) (fun i hi ↦ f_meas i)
      · simp only [Finset.mem_range, Set.mem_Ici, Set.disjoint_iUnion_right,
          Set.disjoint_iUnion_left]
        intro i hi j hj
        exact f_disj (hj.trans_le hi).ne
    have C n : m (⋃ i, f i) - ∑ i ∈ Finset.range n, m (f i) = m (⋃ i ∈ Set.Ici n, f i) := by
      rw [B n, A]; simp
    simp only [C]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun n ↦ μ (⋃ i ∈ Set.Ici n, f i)) ?_ (fun i ↦ bot_le) (fun i ↦ hm _)
    exact tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (fun i ↦ (f_meas i).nullMeasurableSet) f_disj

end MeasureTheory.VectorMeasure
end
