@[expose] public section

noncomputable section

namespace NavierStokes.TerminalStress

open Set Filter MeasureTheory

open SimilarityProfile (partialT partialS partialZ)

open scoped Topology ContDiff

theorem swirlCoefficient_contDiffAt (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f (Real.log (SimilarityProfile.X h p))) :
    ContDiffAt ℝ 2 (swirlCoefficient C h f) p := by
  have hK : ContDiffAt ℝ 2 (physicalHeat C (1 + h)) p :=
    (physicalHeat_contDiffAt C (by linarith only [hh]) ht hs).of_le (WithTop.coe_le_coe.mpr le_top)
  exact (hK.mul (flattening_contDiffAt hh hh1 ht hs hf)).div
    ((contDiffAt_const.mul contDiffAt_snd.fst).sqrt (show 2 * p.2.1 ≠ 0 by positivity))
    (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

end NavierStokes.TerminalStress
end
end
