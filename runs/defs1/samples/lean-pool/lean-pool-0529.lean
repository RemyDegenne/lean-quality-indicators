@[expose] public section

namespace HermitianMat

variable {α R 𝕜 : Type*} {m n : Type*}

variable [Star R] [TrivialStar R]

variable [RCLike 𝕜]

section eigenspace

variable [Fintype n] [DecidableEq n] (A : HermitianMat n 𝕜)

/-- The eigenspace of the linear endomorphism induced by a Hermitian matrix. -/
noncomputable def eigenspace (μ : 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Module.End.eigenspace A.lin μ

end eigenspace
end HermitianMat
end
