public section

noncomputable section

open Filter ContinuousLinearMap

open scoped Topology

variable {𝕜 E F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The spatial Jacobian of a parametric map at `x`, as a function of the parameter. If `F` is not
differentiable at `(t, x)`, its value at `t` is the junk value `0`. -/
def spatialFDeriv (F : 𝕜 × E → F') (x : E) (t : 𝕜) : E →L[𝕜] F' :=
  (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E)

end
end
