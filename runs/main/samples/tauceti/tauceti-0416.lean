public section

noncomputable section

open MeasureTheory Set Metric

open scoped Topology BoundedContinuousFunction

namespace MeasureTheory

variable {E : Type*}

theorem exists_intervalStep_dist_lt [PseudoMetricSpace E] (g : ℝ → E) {a b ε : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hab : a < b) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Icc a b,
      dist (intervalStep a ((b - a) / N) g t) (g t) < ε := by
  obtain ⟨η, hη, hg⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / η)
  have hNpos : (0 : ℝ) < N := (div_pos (sub_pos.mpr hab) hη).trans hN
  have hδ : 0 < (b - a) / N := div_pos (sub_pos.mpr hab) hNpos
  have hmesh : (b - a) / N < η := by
    rw [div_lt_iff₀ hNpos]
    simpa only [mul_comm] using (div_lt_iff₀ hη).mp hN
  refine ⟨N, Nat.cast_pos.mp hNpos, fun t ht ↦ ?_⟩
  obtain ⟨hs0, hs1, hs2⟩ := sample_bounds hδ ht.1
  have hs : a + (⌊(t - a) / ((b - a) / N)⌋₊ : ℝ) * ((b - a) / N) ∈ Icc a b :=
    ⟨hs0, hs1.trans ht.2⟩
  have hd : dist (a + (⌊(t - a) / ((b - a) / N)⌋₊ : ℝ) * ((b - a) / N)) t < η := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs1)]
    linarith
  simpa only [intervalStep] using hg _ hs t ht hd

end MeasureTheory
end
end
