public section

open Function Set

open scoped NNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearEquiv

theorem hasBoundedApproximationPropertyWith (e : E ≃L[𝕜] F) {C : ℝ≥0}
    (h : TauCeti.HasBoundedApproximationPropertyWith 𝕜 E C) :
    TauCeti.HasBoundedApproximationPropertyWith 𝕜 F
      (C * ‖e.toContinuousLinearMap‖₊ * ‖e.symm.toContinuousLinearMap‖₊) :=
  h.of_leftInverse e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply

end ContinuousLinearEquiv
end
