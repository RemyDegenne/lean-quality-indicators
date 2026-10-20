@[expose] public section

noncomputable section

namespace NavierStokes.ValidDyadicBandCover

open Set Filter ProblemStatement PhysicalWaveSum

open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem field_zero_germ {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {N : ℕ} {f : ℕ → SpaceTime → E} (hf : Compatible h N f)
    (hqbig : qbig ≤ ChartScales.Q N) {w : SpaceTime}
    (hw : w ∈ CutStageEstimates.physicalSublevel h qbig)
    (hz : ∀ n, N ≤ n → w ∈ band h n → f n =ᶠ[𝓝 w] fun _ => 0) :
    field h N f =ᶠ[𝓝 w] fun _ => 0 := by
  obtain ⟨n, hn, hband, _⟩ := exists_band hh hh1 N hw.1 (hw.2.le.trans hqbig)
  exact (field_germ hh hh1 hf hn hband).trans (hz n hn hband)

end NavierStokes.ValidDyadicBandCover
end
end
