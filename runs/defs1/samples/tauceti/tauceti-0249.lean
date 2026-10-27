public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {S : Set E}

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- Restriction of an `Lᵖ` value-gradient jet to a smaller open set. -/
def Sobolev1JetLp.restrictL (hU : U ≤ Omega) :
    Sobolev1JetLp mu Omega p →L[ℝ] Sobolev1JetLp mu U p :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    simpa only [one_smul] using
      Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))

end TauCeti
end
end
