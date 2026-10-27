section

@[expose] public section

noncomputable section

namespace EulerDirichletEndpointReduction

open InnerProductSpace ContinuousLinearMap EulerCoerciveProjection

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

variable (S : Submodule ℝ E) [CompleteSpace S]
  (A : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
  (hA : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)

variable [CompleteSpace E]

/-- A prescribed bounded trial lift followed by the actual stationary projection. -/
def endpointExtension (L : U →L[ℝ] E) : U →L[ℝ] E :=
  (stationaryPart S A c hc hA).comp L

end EulerDirichletEndpointReduction
end
end
end
