@[expose] public section

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

theorem norm_mapL_le (f : E →L[𝕜] F) (g : G →L[𝕜] H) : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ := by
  grw [mapL, ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.norm_rTensor_le,
    ContinuousLinearMap.norm_lTensor_le]

end TensorProduct
end
