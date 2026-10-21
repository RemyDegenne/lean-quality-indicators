namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped NNReal Topology

namespace Problem367.PosteriorStoppingTimes

theorem exists_earlier_nnrat {f : ℝ≥0 → ℝ} {t : ℝ≥0} {r : ℝ}
    (hc : ContinuousAt f t) (ht : 0 < t) (hr : r < f t) :
    ∃ q : ℚ≥0, (q : ℝ≥0) < t ∧ r < f (q : ℝ≥0) := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc (f t - r) (sub_pos.mpr hr)
  have htR : (0 : ℝ) < t := ht
  have hlo : max (0 : ℝ) ((t : ℝ) - δ) < t :=
    max_lt htR (sub_lt_self _ hδ)
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlo
  have hq0 : 0 ≤ q := Rat.cast_nonneg.mp (le_of_lt ((le_max_left _ _).trans_lt hqlo))
  let qn : ℚ≥0 := ⟨q, hq0⟩
  have hqn : ((qn : ℝ≥0) : ℝ) = (q : ℝ) := by
    norm_cast
  have hqt : (qn : ℝ≥0) < t := by exact_mod_cast (hqn ▸ hqhi)
  refine ⟨qn, hqt, ?_⟩
  have hd : dist (qn : ℝ≥0) t < δ := by
    rw [NNReal.dist_eq, hqn, abs_of_neg (sub_neg.mpr hqhi)]
    have := (le_max_right (0 : ℝ) ((t : ℝ) - δ)).trans_lt hqlo
    linarith
  have hsmall := hcont hd
  rw [Real.dist_eq] at hsmall
  have hleft := (abs_lt.mp hsmall).1
  linarith

end Problem367.PosteriorStoppingTimes
end
end OAI
