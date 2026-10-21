namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison

variable {D S O : Finset V}

lemma correct_leaf_dominates (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ D) (z : V × ℝ) (hz : z ∈ s.leaves) :
    dist w (C.assign w) ≤ dist w z.1+z.2 := by
  have hh := C.comparison_triangle w z.1 hw (hs.2.2 z hz).1
  have hr := (hs.2.2 z hz).2.2.2.2.1
  linarith

end Comparison
end MetricKMedianRecovery.Sampling
end OAI
