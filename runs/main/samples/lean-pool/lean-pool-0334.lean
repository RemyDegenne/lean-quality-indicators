@[expose] public section

noncomputable section

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {𝕜 : Type*} [RCLike 𝕜]

variable {ι : Type*} [Fintype ι] (S : Submodule 𝕜 (EuclideanSpace 𝕜 n))

variable (A B : HermitianMat n 𝕜)

open scoped InnerProductSpace

@[simp]
theorem kerProj_of_nonSingular [NonSingular A] : A.kerProj = 0 := by
  simp only [kerProj, nonSingular_ker_bot, HermitianMat.ext_iff]
  simp [projector]

end HermitianMat
end
end
