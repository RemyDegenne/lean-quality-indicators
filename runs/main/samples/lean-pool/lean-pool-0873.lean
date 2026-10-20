@[expose] public section

noncomputable section

namespace NavierStokes.BaseRadialJets

open Set Filter Function BaseChartJets PhaseJetBounds PrimaryPulseBounds

open scoped ContDiff Topology BigOperators

theorem normalizedStream_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) : ContDiffAt ℝ ∞ (normalizedStream a h d Q) p := by
  have hc := normalizedCoordinates_smoothAt hh hh1 hT
  have hq := normalizedCoordinates_q_pos hh hh1 hT
  have hcs := (SlowBorelBase.scaleMap Q).contDiff.contDiffAt.comp p hc
  have hs : ContDiffAt ℝ ∞ (SlowBorelBase.slowSum a h (averageSequence d))
      (SlowBorelBase.scaleMap Q (normalizedCoordinates h p)) :=
    SlowBorelBase.slowSum_smoothAt ha (averageSequence_smooth hd) h
      (show 0 < (SlowBorelBase.scaleMap Q (normalizedCoordinates h p)).1 from mul_pos hQ hq)
  have hp : ContDiffAt ℝ ∞ (axialFactor h) p := hc.fst.rpow_const_of_ne hq.ne'
  have hsc := hs.comp p hcs
  apply hp.mul
  exact hsc

end NavierStokes.BaseRadialJets
end
end
