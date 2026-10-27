public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **The Sobolev space `W^{1,p}_0(Ω)`**, the closure of `C_c^∞(Ω)` in `W^{1,p}(Ω)`. -/
abbrev W1p0 (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] := (w1p0Submodule mu Omega p).toSubmodule

end TauCeti
end
end
