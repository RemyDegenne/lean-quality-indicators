@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v w

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

@[simp]
theorem modulus_neg (T : E →L[𝕜] F) : (-T).modulus = T.modulus := by
  rw [modulus_def, modulus_def]
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, map_neg, neg_apply,
    neg_neg]

end ContinuousLinearMap
end
