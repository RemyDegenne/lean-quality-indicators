@[expose] public section

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

open LinearMap

theorem congrL_mul_mul (f : E ≃L[𝕜] E) (g : G ≃L[𝕜] G) (f' : E ≃L[𝕜] E) (g' : G ≃L[𝕜] G) :
    congrL (f * f') (g * g') = congrL f g * congrL f' g' := congrL_trans_trans ..

end TensorProduct
end
