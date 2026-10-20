@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory

open scoped BigOperators ContDiff Topology

open NavierStokes.TerminalCompensation

namespace NavierStokes.ParametricTerminalCompensation

theorem FirstJetWithinBound.toFirstJetBound {P : Patch} {a : ℝ → ℝ} {c : ℝ → Coeff}
    {S : Set ℝ} {η L : ℝ} (h : FirstJetWithinBound P a c S η L) (hS : S ∈ 𝓝 η) :
    FirstJetBound P a c η L := by
  intro x
  simpa only [derivWithin_of_mem_nhds hS] using h x

end NavierStokes.ParametricTerminalCompensation
end
end
