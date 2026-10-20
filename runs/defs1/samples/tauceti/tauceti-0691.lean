public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace

universe u

variable {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

attribute [instance] SobolevStage.instNormedAddCommGroup

attribute [instance] SobolevStage.instNormedSpace

attribute [instance] SobolevStage.instCompleteSpace

attribute [instance] Wkp.instNormedAddCommGroup

attribute [instance] Wkp.instNormedSpace

attribute [instance] Wkp.instCompleteSpace

namespace Wkp

/-- The continuous projection to the highest weak derivative of a positive-order Sobolev
function.  For `W^{k+1,p}` its target is `Lᵖ(Ω; IteratedGradient E k)`. -/
def iteratedGradientL (k : ℕ) : Wkp mu Omega p (k + 1) →L[ℝ]
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL

end Wkp
end TauCeti
end
end
