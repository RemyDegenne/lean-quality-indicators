@[expose] public section

open Filter

open scoped Topology

namespace LocalComplexGeometry

noncomputable section

namespace LocalBiholomorphAt

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  {a : E} {b : F} {c : G}

/-- An analytic map with bijective derivative is locally biholomorphic. -/
def ofAnalyticAtOfBijectiveFDeriv [CompleteSpace E] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (hbij : Function.Bijective (fderiv ℂ f a)) :
    LocalBiholomorphAt E F a (f a) := by
  let e : E ≃L[ℂ] F := ContinuousLinearEquiv.ofBijective (fderiv ℂ f a)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  apply ofAnalyticAtOfFDerivEquiv hf e
  rfl

end LocalBiholomorphAt
end
end LocalComplexGeometry
end
