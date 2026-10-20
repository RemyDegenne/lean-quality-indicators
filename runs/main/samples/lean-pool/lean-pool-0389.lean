@[expose] public section

namespace NavierStokes.MeanChartCompatibility

noncomputable section

open Set Function Filter MeasureTheory

open scoped Topology ContDiff BigOperators Interval

section Pullback

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem graphDr_pull (l : ℝ) (C : E →L[ℝ] F) (u : ℝ)
    (knew kold : ℝ → ℝ) (v : E) (w : F) {f : ℝ × F → ℝ} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f (chartLinear l C z))
    (hvector : C (knew z.1 • v) = l • (kold (l * z.1) • w)) :
    PressureStream.graphDr knew v (pull l C u f) z =
      (u * l) * PressureStream.graphDr kold w f (chartLinear l C z) := by
  rw [PressureStream.graphDr, fderiv_pull_apply l C u hf]
  have he : chartLinear l C (PressureStream.radialVector knew v z) =
      l • PressureStream.radialVector kold w (chartLinear l C z) := by
    apply Prod.ext
    · simp only [PressureStream.radialVector, chartLinear_apply, mul_one, map_smul, Prod.smul_mk,
        smul_eq_mul]
    · exact hvector
  rw [he, map_smul]
  simp only [smul_eq_mul, PressureStream.graphDr]
  ring

end Pullback
end
end NavierStokes.MeanChartCompatibility
end
