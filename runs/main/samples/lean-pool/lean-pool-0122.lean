@[expose] public section

namespace NavierStokes.PhysicalCurlCovariance

open Set Filter Function

open ProblemStatement HarmonicCalculus

open scoped Topology ContDiff

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open PhysicalResidualBridge (commonGraph)

theorem spatialCurl_zero_of_zero_near {A : VelocityField} {z : SpaceTime}
    (hA : A =ᶠ[𝓝 z] fun _ => 0) : SpatialCurl.spatialCurl A z = 0 := by
  have hs : (fun y => A (z.1, y)) =ᶠ[𝓝 z.2] fun _ => 0 :=
    hA.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  change SpatialCurl.curl (fun y => A (z.1, y)) z.2 = 0
  rw [SpatialCurl.curl_eq_of_eventuallyEq hs]
  simp only [SpatialCurl.curl, fderiv_fun_const, Pi.zero_apply, map_zero]

end
end NavierStokes.PhysicalCurlCovariance
end
