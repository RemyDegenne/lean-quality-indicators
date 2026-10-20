section

@[expose] public section

noncomputable section

namespace NavierStokes.ActivationBounds

open Set Filter MeasureTheory Metric ProfileHistories StressActivation

open scoped Topology ContDiff

theorem history_uniform_jets (X0 : ℝ) (initial : HistoryRow → ℝ → ℝ)
    {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K) (hKJ : K ⊆ J) {L U : ProfileHistories.Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (T0 : ℝ) (r : HistoryRow) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Ioc (0 : ℝ) T0, ∀ κ ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ Icc (0 : ℝ) T, ∀ η ∈ K,
        |iteratedDeriv n (fun ξ =>
          logHistory X0 initial (activatedAngular T κ L) (controlled T κ U) r (y, ξ) -
            logHistory X0 initial (referenceAngular L) U r (y, ξ)) η| ≤
              M * y * activation T κ y := by
  apply width_uniform_jet_bound hJ hK hKJ (historyErrorFactor_smooth X0 hJ hL hU r)
  intro κ T hT u η hη
  exact history_scaled_factor hT.ne' κ X0 initial hJ hL hU r u hη

end NavierStokes.ActivationBounds
end
end
end
