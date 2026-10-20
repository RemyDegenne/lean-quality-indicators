public section

namespace TauCeti

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The trace of a continuous endomorphism of a finite-dimensional space, as a continuous linear
functional. Continuity is automatic: `V →L[𝕜] V` is finite-dimensional over the complete field
`𝕜`, and every linear map out of such a space is continuous. -/
noncomputable def traceCLM : (V →L[𝕜] V) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace 𝕜 V).comp (ContinuousLinearMap.coeLM 𝕜))

end TauCeti
end
