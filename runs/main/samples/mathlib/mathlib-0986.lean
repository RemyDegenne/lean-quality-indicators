@[expose] public section

variable {𝕜 E F G : Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open NNReal Filter ENNReal Set Asymptotics

open scoped Topology Pointwise

section

variable {f g : E → F} {p pf : FormalMultilinearSeries 𝕜 E F} {s t : Set E} {x : E} {r r' : ℝ≥0∞}

variable (𝕜)

variable {𝕜}

theorem HasFPowerSeriesOnBall.mono (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 0 < r')
    (hr : r' ≤ r) : HasFPowerSeriesOnBall f p x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (Metric.eball_subset_eball hr hy)⟩

end
end
