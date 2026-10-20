@[expose] public section

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

theorem offDiagonalPart_eq (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) : U.offDiagonalPart A = A - U.diagonalPart A := by
  simp only [offDiagonalPart]

end Submodule
end
