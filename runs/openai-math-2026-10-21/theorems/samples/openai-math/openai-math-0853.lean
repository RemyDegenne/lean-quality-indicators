namespace OAI

noncomputable section

namespace SharpLiebThirring.OperatorProof

open MeasureTheory Set Filter

open scoped Topology BoundedContinuousFunction

lemma cutoffLM_norm (s : Set ℝ) (hs : MeasurableSet s) (f : L2C) :
    ‖cutoffLM s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(cutoff_memLp s hs f).coeFn_toLp] with x hx
  change ‖((cutoff_memLp s hs f).toLp (s.indicator f)) x‖ ≤ _
  rw [hx]
  exact norm_indicator_le_norm_self _ _

end SharpLiebThirring.OperatorProof
end
end OAI
