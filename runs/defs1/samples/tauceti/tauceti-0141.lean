public section

noncomputable section

open Set

open scoped ContDiff

namespace ContinuousLinearMap.FredholmPackage

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : E →L[𝕜] F} (pkg : ContinuousLinearMap.FredholmPackage T)

section Chart

variable [CompleteSpace E]

/-- The finite-dimensional obstruction map obtained by fixing the essential codomain coordinate.
Both its domain and codomain are finite dimensional. This is the map to which finite-dimensional
Sard is applied in the Lyapunov--Schmidt proof of Sard--Smale. -/
def obstructionSlice {f : E → F} {a : E} (hf : HasStrictFDerivAt f T a)
    (y : pkg.decCodom.X₁) (z : pkg.decDom.X₀) : pkg.decCodom.X₀ :=
  pkg.obstructionMap hf (y, z)

end Chart
end ContinuousLinearMap.FredholmPackage
end
end
