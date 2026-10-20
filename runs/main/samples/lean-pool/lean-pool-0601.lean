@[expose] public section

noncomputable section

universe u

namespace NavierStokes.PhysicalStageSupport

open Set Function Filter ProblemStatement PhysicalStageBounds

open MixedDiagonalExtensions

open scoped Topology ContDiff BigOperators

section Increments

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

theorem potentialIncrement_support (W : WaveData h D I K (Fin 3))
    (M : MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig R : ℝ}
    (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hW : W.upperRadius ≤ 2 * R) (hM : M.upperRadius ≤ R) :
    SublevelShrinkingSupport h (outerConstant R) qbig (potentialIncrement W M) :=
  support_add (wave_vector_support W hW) (mean_angular_support M hh hh1 hq hM)

end Increments
end NavierStokes.PhysicalStageSupport
end
end
