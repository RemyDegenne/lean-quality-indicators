public section

noncomputable section

namespace Submodule

open Module Module.End

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

@[simp]
theorem sinThetaMap_self : U.sinThetaMap U = 0 :=
  (sinThetaMap_eq_zero_iff U U).2 le_rfl

end Submodule
end
end
