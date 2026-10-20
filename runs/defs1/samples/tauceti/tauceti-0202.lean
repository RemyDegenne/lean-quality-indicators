public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega Omega' Omega'' : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Extension by zero as an operator `W^{1,p}_0(Ω) →L[ℝ] W^{1,p}_0(Ω')`.**  The extension of a
limit of test functions on `Ω` is again a limit of test functions, on `Ω'`, so the operator lands
in `W^{1,p}_0(Ω')` and not merely in `W^{1,p}(Ω')`; compose with
`(TauCeti.w1p0Submodule mu Omega' p).toSubmodule.subtypeL` for the `W^{1,p}(Ω')`-valued map.
Taking `Ω' = ⊤`, that is `hsub = le_top`, gives the extension operator to the whole space. -/
def W1p0.extendByZeroL (hsub : Omega ≤ Omega') :
    W1p0 mu Omega p →L[ℝ] W1p0 mu Omega' p :=
  ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.codRestrict
      ((Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub).toContinuousLinearMap.comp
        ((w1pSubmodule mu Omega p).toSubmodule.subtypeL.comp
          (w1p0Submodule mu Omega p).toSubmodule.subtypeL))
      (w1pSubmodule mu Omega' p).toSubmodule
      fun u => Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule hsub u.2)
    (w1p0Submodule mu Omega' p).toSubmodule
    fun u => mem_w1p0Submodule_of_coe_eq hsub u.2 rfl

end TauCeti
end
end
