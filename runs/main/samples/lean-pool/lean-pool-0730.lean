@[expose] public section

noncomputable section

namespace NavierStokes.PhysicalMeanJetBounds

open Set Function Filter ProblemStatement PhysicalWaveSum LocalPhysicalCopyBounds

open scoped Topology ContDiff BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem graph_slow_continuous (h : ℝ) (n d : ℕ) :
    Continuous (fun w => (graph h n d w).2.1) := by
  simp_rw [graph_slow]
  exact ((continuous_const.sub continuous_fst).div_const _).prodMk
    (continuous_const.mul ((AxisymmetricFields.projection 2).continuous.comp continuous_snd))

end NavierStokes.PhysicalMeanJetBounds
end
end
